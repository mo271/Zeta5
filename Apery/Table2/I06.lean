import Apery.Table2.U06
import Apery.Table2.U07

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_240 : (13483592882995377182008513774678397 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1552066066561 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1552066066561 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (44046368558613 / 100000000000000 : ℝ) ≤ Real.sqrt (1552066066561 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1552066066561 / 8000000000000 : ℝ) ≤ (22023184279307 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (22023184279307 / 50000000000000 : ℝ) = (50000000000000 / 22023184279307 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (44046368558613 / 100000000000000 : ℝ) = (2500000000000 / 14682122852871 : ℝ) := by norm_num
  have hL1 : (14185274517 / 80000000000 : ℝ) ≤ Real.log (1 + (1552066066561 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1552066066561 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-161127330335499 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (22023184279307 / 50000000000000 : ℝ) ≤ (414895284704387 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (115590104209050961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 22023184279307 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 22023184279307 : ℝ) = (22023184279307 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 14682122852871 : ℝ) ≤ (5270547565071 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (115590104209050961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (22023184279307 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (44046368558613 / 100000000000000 : ℝ)) ≤ (5270547565071 / 31250000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_240 : ∀ t : ℝ, (1552066066561 / 8000000000000 : ℝ) < t → t ≤ (201105762729 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-49507833126047573256452399 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (201105762729 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_241
  have hV : (13483592882995377182008513774678397 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1552066066561 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_240 (Vfield_monotoneOn (show (1552066066561 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1552066066561 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_241 : (13746370809425725482663250849328897 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (201105762729 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (201105762729 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (44844817173113 / 100000000000000 : ℝ) ≤ Real.sqrt (201105762729 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (201105762729 / 1000000000000 : ℝ) ≤ (22422408586557 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (22422408586557 / 50000000000000 : ℝ) = (50000000000000 / 22422408586557 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (44844817173113 / 100000000000000 : ℝ) = (7500000000000 / 44844817173113 : ℝ) := by norm_num
  have hL1 : (18324260144291 / 100000000000000 : ℝ) ≤ Real.log (1 + (201105762729 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((201105762729 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-157633799467833 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (22422408586557 / 50000000000000 : ℝ) ≤ (421562675308691 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (114923365148620561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 22422408586557 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 22422408586557 : ℝ) = (22422408586557 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 44844817173113 : ℝ) ≤ (41427444352849 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (114923365148620561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (22422408586557 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (44844817173113 / 100000000000000 : ℝ)) ≤ (41427444352849 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_241 : ∀ t : ℝ, (201105762729 / 1000000000000 : ℝ) < t → t ≤ (3251812320751 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-12229887631211560522023777 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3251812320751 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_242
  have hV : (13746370809425725482663250849328897 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (201105762729 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_241 (Vfield_monotoneOn (show (201105762729 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (201105762729 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_242 : (13824582621165433918646499541325293 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3251812320751 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3251812320751 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (45081955375397 / 100000000000000 : ℝ) ≤ Real.sqrt (3251812320751 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3251812320751 / 16000000000000 : ℝ) ≤ (22540977687699 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (22540977687699 / 50000000000000 : ℝ) = (50000000000000 / 22540977687699 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (45081955375397 / 100000000000000 : ℝ) = (7500000000000 / 45081955375397 : ℝ) := by norm_num
  have hL1 : (9250824029751 / 50000000000000 : ℝ) ≤ Real.log (1 + (3251812320751 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3251812320751 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4893985783213 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (22540977687699 / 50000000000000 : ℝ) ≤ (105883814662613 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (114726106814444461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 22540977687699 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 22540977687699 : ℝ) = (22540977687699 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 45081955375397 : ℝ) ≤ (412134662867 / 2500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (114726106814444461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (22540977687699 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (45081955375397 / 100000000000000 : ℝ)) ≤ (412134662867 / 2500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_242 : ∀ t : ℝ, (3251812320751 / 16000000000000 : ℝ) < t → t ≤ (1642966218919 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-194403343617377432476799129 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1642966218919 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_243
  have hV : (13824582621165433918646499541325293 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3251812320751 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_242 (Vfield_monotoneOn (show (3251812320751 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3251812320751 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_243 : (6951229508203262089979345087929221 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1642966218919 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1642966218919 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (22658926351709 / 50000000000000 : ℝ) ≤ Real.sqrt (1642966218919 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1642966218919 / 8000000000000 : ℝ) ≤ (45317852703419 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (45317852703419 / 100000000000000 : ℝ) = (100000000000000 / 45317852703419 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (22658926351709 / 50000000000000 : ℝ) = (3750000000000 / 22658926351709 : ℝ) := by norm_num
  have hL1 : (3735744373419 / 20000000000000 : ℝ) ≤ Real.log (1 + (1642966218919 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1642966218919 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-155591715741523 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (45317852703419 / 100000000000000 : ℝ) ≤ (425494045374953 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (114530228141994361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 45317852703419 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 45317852703419 : ℝ) = (45317852703419 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 22658926351709 : ℝ) ≤ (164011080883073 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (114530228141994361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (45317852703419 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (22658926351709 / 50000000000000 : ℝ)) ≤ (164011080883073 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_243 : ∀ t : ℝ, (1642966218919 / 8000000000000 : ℝ) < t → t ≤ (132802102197 / 640000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-96657010654220661958918899 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (132802102197 / 640000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_244
  have hV : (6951229508203262089979345087929221 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1642966218919 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_243 (Vfield_monotoneOn (show (1642966218919 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1642966218919 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_244 : (109218781912615896596441004053831 / 39062500000000000000000000000000 : ℝ) ≤ Vfield (132802102197 / 640000000000 : ℝ) := by
  have hp : (0 : ℝ) < (132802102197 / 640000000000 : ℝ) := by norm_num
  have hs1 : (355879128399 / 781250000000 : ℝ) ≤ Real.sqrt (132802102197 / 640000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (132802102197 / 640000000000 : ℝ) ≤ (45552528435073 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (45552528435073 / 100000000000000 : ℝ) = (100000000000000 / 45552528435073 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (355879128399 / 781250000000 : ℝ) = (19531250000 / 118626376133 : ℝ) := by norm_num
  have hL1 : (1885548267751 / 10000000000000 : ℝ) ≤ Real.log (1 + (132802102197 / 640000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((132802102197 / 640000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-154586101828181 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (45552528435073 / 100000000000000 : ℝ) ≤ (85487848809793 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (114335708274593161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 45552528435073 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 45552528435073 : ℝ) = (45552528435073 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (19531250000 / 118626376133 : ℝ) ≤ (10198818274893 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (114335708274593161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (45552528435073 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (355879128399 / 781250000000 : ℝ)) ≤ (10198818274893 / 62500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_244 : ∀ t : ℝ, (132802102197 / 640000000000 : ℝ) < t → t ≤ (6674225226937 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-38561915841943789623664033 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6674225226937 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_245
  have hV : (109218781912615896596441004053831 / 39062500000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (132802102197 / 640000000000 : ℝ) := by norm_num
    refine le_trans V_pt_244 (Vfield_monotoneOn (show (132802102197 / 640000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (132802102197 / 640000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_245 : (3504663406798468948212208612545133 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (6674225226937 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6674225226937 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (11417353522757 / 25000000000000 : ℝ) ≤ Real.sqrt (6674225226937 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6674225226937 / 32000000000000 : ℝ) ≤ (45669414091029 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (45669414091029 / 100000000000000 : ℝ) = (100000000000000 / 45669414091029 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (11417353522757 / 25000000000000 : ℝ) = (1875000000000 / 11417353522757 : ℝ) := by norm_num
  have hL1 : (18943746054179 / 100000000000000 : ℝ) ≤ Real.log (1 + (6674225226937 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6674225226937 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1232696494761 / 800000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (45669414091029 / 100000000000000 : ℝ) ≤ (428406811619467 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (114238951517542961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 45669414091029 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 45669414091029 : ℝ) = (45669414091029 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 11417353522757 : ℝ) ≤ (162770795954461 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (114238951517542961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (45669414091029 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (11417353522757 / 25000000000000 : ℝ)) ≤ (162770795954461 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_245 : ∀ t : ℝ, (6674225226937 / 32000000000000 : ℝ) < t → t ≤ (838543168003 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-192324902054174840596013037 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (838543168003 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_246
  have hV : (3504663406798468948212208612545133 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6674225226937 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_245 (Vfield_monotoneOn (show (6674225226937 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6674225226937 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_246 : (14057221834782237459747030022080183 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (838543168003 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (838543168003 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (45786001354207 / 100000000000000 : ℝ) ≤ Real.sqrt (838543168003 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (838543168003 / 4000000000000 : ℝ) ≤ (1430812542319 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1430812542319 / 3125000000000 : ℝ) = (3125000000000 / 1430812542319 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (45786001354207 / 100000000000000 : ℝ) = (7500000000000 / 45786001354207 : ℝ) := by norm_num
  have hL1 : (9515965797653 / 50000000000000 : ℝ) ≤ Real.log (1 + (838543168003 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((838543168003 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-30718099981957 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1430812542319 / 3125000000000 : ℝ) ≤ (214685529023657 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (114142526874758261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 1430812542319 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 1430812542319 : ℝ) = (1430812542319 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 45786001354207 : ℝ) ≤ (162363579123607 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (114142526874758261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1430812542319 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (45786001354207 / 100000000000000 : ℝ)) ≤ (162363579123607 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_246 : ∀ t : ℝ, (838543168003 / 4000000000000 : ℝ) < t → t ≤ (6742465461111 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-191856734203968633710973859 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6742465461111 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_247
  have hV : (14057221834782237459747030022080183 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (838543168003 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_246 (Vfield_monotoneOn (show (838543168003 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (838543168003 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_247 : (7047854598144436393997423177131353 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (6742465461111 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6742465461111 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (22951146249137 / 50000000000000 : ℝ) ≤ Real.sqrt (6742465461111 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6742465461111 / 32000000000000 : ℝ) ≤ (1836091699931 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1836091699931 / 4000000000000 : ℝ) = (4000000000000 / 1836091699931 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (22951146249137 / 50000000000000 : ℝ) = (3750000000000 / 22951146249137 : ℝ) := by norm_num
  have hL1 : (19120039438051 / 100000000000000 : ℝ) ≤ Real.log (1 + (6742465461111 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6742465461111 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-153096391533577 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1836091699931 / 4000000000000 : ℝ) ≤ (4303320079729 / 10000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (114046431882199661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 1836091699931 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 1836091699931 : ℝ) = (1836091699931 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 22951146249137 : ℝ) ≤ (40489850892513 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (114046431882199661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1836091699931 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (22951146249137 / 50000000000000 : ℝ)) ≤ (40489850892513 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_247 : ∀ t : ℝ, (6742465461111 / 32000000000000 : ℝ) < t → t ≤ (3388292789099 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-4785067359632748827953227 / 2500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3388292789099 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_248
  have hV : (7047854598144436393997423177131353 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6742465461111 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_247 (Vfield_monotoneOn (show (6742465461111 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6742465461111 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_248 : (2826823239122457030455282590348777 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (3388292789099 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3388292789099 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (9203657953633 / 20000000000000 : ℝ) ≤ Real.sqrt (3388292789099 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3388292789099 / 16000000000000 : ℝ) ≤ (23009144884083 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (23009144884083 / 50000000000000 : ℝ) = (50000000000000 / 23009144884083 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9203657953633 / 20000000000000 : ℝ) = (1500000000000 / 9203657953633 : ℝ) := by norm_num
  have hL1 : (19208069719209 / 100000000000000 : ℝ) ≤ Real.log (1 + (3388292789099 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3388292789099 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-30520942517827 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (23009144884083 / 50000000000000 : ℝ) ≤ (431289685734357 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113950664106053961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 23009144884083 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 23009144884083 : ℝ) = (23009144884083 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 9203657953633 : ℝ) ≤ (40389557905737 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113950664106053961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (23009144884083 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9203657953633 / 20000000000000 : ℝ)) ≤ (40389557905737 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_248 : ∀ t : ℝ, (3388292789099 / 16000000000000 : ℝ) < t → t ≤ (1362141139057 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-190960975798462754088746551 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1362141139057 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_249
  have hV : (2826823239122457030455282590348777 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3388292789099 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_248 (Vfield_monotoneOn (show (3388292789099 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3388292789099 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_249 : (885777706994059434787182052174703 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (1362141139057 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1362141139057 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (2883374711287 / 6250000000000 : ℝ) ≤ Real.sqrt (1362141139057 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1362141139057 / 6400000000000 : ℝ) ≤ (46133995380593 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (46133995380593 / 100000000000000 : ℝ) = (100000000000000 / 46133995380593 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2883374711287 / 6250000000000 : ℝ) = (468750000000 / 2883374711287 : ℝ) := by norm_num
  have hL1 : (3859204515043 / 20000000000000 : ℝ) ≤ Real.log (1 + (1362141139057 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1362141139057 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38028859825811 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (46133995380593 / 100000000000000 : ℝ) ≤ (86448823074557 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113855221142211161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 46133995380593 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 46133995380593 : ℝ) = (46133995380593 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (468750000000 / 2883374711287 : ℝ) ≤ (6446401050461 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113855221142211161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (46133995380593 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2883374711287 / 6250000000000 : ℝ)) ≤ (6446401050461 / 40000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_249 : ∀ t : ℝ, (1362141139057 / 6400000000000 : ℝ) < t → t ≤ (1711206453093 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-95265083469328085795665517 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1711206453093 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_250
  have hV : (885777706994059434787182052174703 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1362141139057 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_249 (Vfield_monotoneOn (show (1362141139057 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1362141139057 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_250 : (14210691019637246092398139358185491 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1711206453093 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1711206453093 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (46249411524539 / 100000000000000 : ℝ) ≤ Real.sqrt (1711206453093 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1711206453093 / 8000000000000 : ℝ) ≤ (2312470576227 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2312470576227 / 5000000000000 : ℝ) = (5000000000000 / 2312470576227 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (46249411524539 / 100000000000000 : ℝ) = (7500000000000 / 46249411524539 : ℝ) := by norm_num
  have hL1 : (9691949071073 / 50000000000000 : ℝ) ≤ Real.log (1 + (1711206453093 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1711206453093 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-151628548249937 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2312470576227 / 5000000000000 : ℝ) ≤ (86639064127477 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113760100615751161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 2312470576227 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 2312470576227 : ℝ) = (2312470576227 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 46249411524539 : ℝ) ≤ (80382375550367 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113760100615751161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2312470576227 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (46249411524539 / 100000000000000 : ℝ)) ≤ (80382375550367 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_250 : ∀ t : ℝ, (1711206453093 / 8000000000000 : ℝ) < t → t ≤ (13723771741831 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-190318491964940762771800917 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (13723771741831 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_251
  have hV : (14210691019637246092398139358185491 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1711206453093 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_250 (Vfield_monotoneOn (show (1711206453093 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1711206453093 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_251 : (3557446310575158859727075042831783 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (13723771741831 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (13723771741831 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (11576752930607 / 25000000000000 : ℝ) ≤ Real.sqrt (13723771741831 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (13723771741831 / 64000000000000 : ℝ) ≤ (46307011722429 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (46307011722429 / 100000000000000 : ℝ) = (100000000000000 / 46307011722429 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (11576752930607 / 25000000000000 : ℝ) = (1875000000000 / 11576752930607 : ℝ) := by norm_num
  have hL1 : (19427806984633 / 100000000000000 : ℝ) ≤ Real.log (1 + (13723771741831 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((13723771741831 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-151385988833181 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (46307011722429 / 100000000000000 : ℝ) ≤ (433669721472547 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113712660532234961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 46307011722429 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 46307011722429 : ℝ) = (46307011722429 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 11576752930607 : ℝ) ≤ (160568201145629 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113712660532234961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (46307011722429 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (11576752930607 / 25000000000000 : ℝ)) ≤ (160568201145629 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_251 : ∀ t : ℝ, (13723771741831 / 64000000000000 : ℝ) < t → t ≤ (6878945929459 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-38021827711626062847255289 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6878945929459 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_252
  have hV : (3557446310575158859727075042831783 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (13723771741831 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_251 (Vfield_monotoneOn (show (13723771741831 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (13723771741831 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_252 : (2849771957731948745349606115401381 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (6878945929459 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6878945929459 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (9272908072349 / 20000000000000 : ℝ) ≤ Real.sqrt (6878945929459 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6878945929459 / 32000000000000 : ℝ) ≤ (23182270180873 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (23182270180873 / 50000000000000 : ℝ) = (50000000000000 / 23182270180873 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9272908072349 / 20000000000000 : ℝ) = (1500000000000 / 9272908072349 : ℝ) := by norm_num
  have hL1 : (9735848277859 / 50000000000000 : ℝ) ≤ Real.log (1 + (6878945929459 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6878945929459 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15114401634377 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (23182270180873 / 50000000000000 : ℝ) ≤ (217071662495229 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113665300180443861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 23182270180873 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 23182270180873 : ℝ) = (23182270180873 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 9272908072349 : ℝ) ≤ (160372370377277 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113665300180443861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (23182270180873 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9272908072349 / 20000000000000 : ℝ)) ≤ (160372370377277 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_252 : ∀ t : ℝ, (6878945929459 / 32000000000000 : ℝ) < t → t ≤ (2758402395201 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-37980399495000968994399111 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2758402395201 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_253
  have hV : (2849771957731948745349606115401381 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6878945929459 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_252 (Vfield_monotoneOn (show (6878945929459 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6878945929459 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_253 : (1426791471673490524488617229990957 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (2758402395201 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2758402395201 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (4642199770853 / 10000000000000 : ℝ) ≤ Real.sqrt (2758402395201 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2758402395201 / 12800000000000 : ℝ) ≤ (46421997708531 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (46421997708531 / 100000000000000 : ℝ) = (100000000000000 / 46421997708531 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4642199770853 / 10000000000000 : ℝ) = (750000000000 / 4642199770853 : ℝ) := by norm_num
  have hL1 : (4878891718077 / 25000000000000 : ℝ) ≤ Real.log (1 + (2758402395201 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2758402395201 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-75451313974077 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (46421997708531 / 100000000000000 : ℝ) ≤ (217308067039949 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113618019271499861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 46421997708531 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 46421997708531 : ℝ) = (46421997708531 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (750000000000 / 4642199770853 : ℝ) ≤ (160177254420177 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113618019271499861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (46421997708531 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4642199770853 / 10000000000000 : ℝ)) ≤ (160177254420177 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_253 : ∀ t : ℝ, (2758402395201 / 12800000000000 : ℝ) < t → t ≤ (3456533023273 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-94848484580573904927547937 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3456533023273 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_254
  have hV : (1426791471673490524488617229990957 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2758402395201 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_253 (Vfield_monotoneOn (show (2758402395201 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2758402395201 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_254 : (571478003370561841667323615870903 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (3456533023273 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3456533023273 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (1859175361087 / 4000000000000 : ℝ) ≤ Real.sqrt (3456533023273 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3456533023273 / 16000000000000 : ℝ) ≤ (5809923003397 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5809923003397 / 12500000000000 : ℝ) = (12500000000000 / 5809923003397 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1859175361087 / 4000000000000 : ℝ) = (300000000000 / 1859175361087 : ℝ) := by norm_num
  have hL1 : (19559417951291 / 100000000000000 : ℝ) ≤ Real.log (1 + (3456533023273 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3456533023273 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-602647283333 / 400000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5809923003397 / 12500000000000 : ℝ) ≤ (435088151612291 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113570817518260561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 5809923003397 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 5809923003397 : ℝ) = (5809923003397 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (300000000000 / 1859175361087 : ℝ) ≤ (159982848936019 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113570817518260561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5809923003397 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1859175361087 / 4000000000000 : ℝ)) ≤ (159982848936019 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_254 : ∀ t : ℝ, (3456533023273 / 16000000000000 : ℝ) < t → t ≤ (13860252210179 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1480421582482420853982027 / 781250000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (13860252210179 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_255
  have hV : (571478003370561841667323615870903 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3456533023273 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_254 (Vfield_monotoneOn (show (3456533023273 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3456533023273 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_255 : (14305965948706172030839471986415667 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (13860252210179 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (13860252210179 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (46536699580443 / 100000000000000 : ℝ) ≤ Real.sqrt (13860252210179 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (13860252210179 / 64000000000000 : ℝ) ≤ (11634174895111 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (11634174895111 / 25000000000000 : ℝ) = (25000000000000 / 11634174895111 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (46536699580443 / 100000000000000 : ℝ) = (2500000000000 / 15512233193481 : ℝ) := by norm_num
  have hL1 : (19603249809531 / 100000000000000 : ℝ) ≤ Real.log (1 + (13860252210179 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((13860252210179 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-150421592206251 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (11634174895111 / 25000000000000 : ℝ) ≤ (87111876088379 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113523694635300161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 11634174895111 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 11634174895111 : ℝ) = (11634174895111 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 15512233193481 : ℝ) ≤ (79894574811633 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113523694635300161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (11634174895111 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (46536699580443 / 100000000000000 : ℝ)) ≤ (79894574811633 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_255 : ∀ t : ℝ, (13860252210179 / 64000000000000 : ℝ) < t → t ≤ (6947186163633 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9464644704589211834350407 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6947186163633 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_256
  have hV : (14305965948706172030839471986415667 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (13860252210179 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_255 (Vfield_monotoneOn (show (13860252210179 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (13860252210179 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_256 : (7162481183621680552233774995220829 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (6947186163633 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6947186163633 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (23296972314741 / 50000000000000 : ℝ) ≤ Real.sqrt (6947186163633 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6947186163633 / 32000000000000 : ℝ) ≤ (46593944629483 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (46593944629483 / 100000000000000 : ℝ) = (100000000000000 / 46593944629483 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23296972314741 / 50000000000000 : ℝ) = (1250000000000 / 7765657438247 : ℝ) := by norm_num
  have hL1 : (1964706246387 / 10000000000000 : ℝ) ≤ Real.log (1 + (6947186163633 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6947186163633 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-150181939294429 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (46593944629483 / 100000000000000 : ℝ) ≤ (436029823405941 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113476650338895561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 46593944629483 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 46593944629483 : ℝ) = (46593944629483 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 7765657438247 : ℝ) ≤ (159596152216751 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113476650338895561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (46593944629483 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23296972314741 / 50000000000000 : ℝ)) ≤ (159596152216751 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_256 : ∀ t : ℝ, (6947186163633 / 32000000000000 : ℝ) < t → t ≤ (13928492444353 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-94546843408109469964581673 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (13928492444353 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_257
  have hV : (7162481183621680552233774995220829 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6947186163633 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_256 (Vfield_monotoneOn (show (6947186163633 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6947186163633 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_257 : (14343939396781686436435764533465653 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (13928492444353 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (13928492444353 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (46651119433837 / 100000000000000 : ℝ) ≤ Real.sqrt (13928492444353 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (13928492444353 / 64000000000000 : ℝ) ≤ (23325559716919 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (23325559716919 / 50000000000000 : ℝ) = (50000000000000 / 23325559716919 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (46651119433837 / 100000000000000 : ℝ) = (7500000000000 / 46651119433837 : ℝ) := by norm_num
  have hL1 : (2461356991391 / 12500000000000 : ℝ) ≤ Real.log (1 + (13928492444353 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((13928492444353 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7497142967247 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (23325559716919 / 50000000000000 : ℝ) ≤ (218249741662383 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113429684347013061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 23325559716919 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 23325559716919 : ℝ) = (23325559716919 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 46651119433837 : ℝ) ≤ (39850963121823 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113429684347013061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (23325559716919 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (46651119433837 / 100000000000000 : ℝ)) ≤ (39850963121823 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_257 : ∀ t : ℝ, (13928492444353 / 64000000000000 : ℝ) < t → t ≤ (87266328509 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-188896269673846879333005113 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (87266328509 / 400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_258
  have hV : (14343939396781686436435764533465653 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (13928492444353 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_257 (Vfield_monotoneOn (show (13928492444353 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (13928492444353 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_258 : (14362897093953127521476643569830047 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (87266328509 / 400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (87266328509 / 400000000000 : ℝ) := by norm_num
  have hs1 : (46708224251463 / 100000000000000 : ℝ) ≤ Real.sqrt (87266328509 / 400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (87266328509 / 400000000000 : ℝ) ≤ (5838528031433 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5838528031433 / 12500000000000 : ℝ) = (12500000000000 / 5838528031433 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (46708224251463 / 100000000000000 : ℝ) = (2500000000000 / 15569408083821 : ℝ) := by norm_num
  have hL1 : (2466828778513 / 12500000000000 : ℝ) ≤ Real.log (1 + (87266328509 / 400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((87266328509 / 400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-149704349624641 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5838528031433 / 12500000000000 : ℝ) ≤ (109242090750487 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113382796379294861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 5838528031433 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 5838528031433 : ℝ) = (5838528031433 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 15569408083821 : ℝ) ≤ (159212246241299 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113382796379294861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5838528031433 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (46708224251463 / 100000000000000 : ℝ)) ≤ (159212246241299 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_258 : ∀ t : ℝ, (87266328509 / 400000000000 : ℝ) < t → t ≤ (13996732678527 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-188700576863662434767081773 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (13996732678527 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_259
  have hV : (14362897093953127521476643569830047 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (87266328509 / 400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_258 (Vfield_monotoneOn (show (87266328509 / 400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (87266328509 / 400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_259 : (7190917757559062320469297768381299 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (13996732678527 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (13996732678527 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (23382629669371 / 50000000000000 : ℝ) ≤ Real.sqrt (13996732678527 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (13996732678527 / 64000000000000 : ℝ) ≤ (46765259338743 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (46765259338743 / 100000000000000 : ℝ) = (100000000000000 / 46765259338743 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23382629669371 / 50000000000000 : ℝ) = (3750000000000 / 23382629669371 : ℝ) := by norm_num
  have hL1 : (4944596342893 / 25000000000000 : ℝ) ≤ Real.log (1 + (13996732678527 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((13996732678527 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-149466407419897 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (46765259338743 / 100000000000000 : ℝ) ≤ (109359116306119 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113335986157042061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 46765259338743 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 46765259338743 : ℝ) = (46765259338743 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 23382629669371 : ℝ) ≤ (159021329320387 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113335986157042061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (46765259338743 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23382629669371 / 50000000000000 : ℝ)) ≤ (159021329320387 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_259 : ∀ t : ℝ, (13996732678527 / 64000000000000 : ℝ) < t → t ≤ (7015426397807 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-37701309458564395572002357 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7015426397807 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_260
  have hV : (7190917757559062320469297768381299 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (13996732678527 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_259 (Vfield_monotoneOn (show (13996732678527 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (13996732678527 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_260 : (7200377358183543311689144662159943 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (7015426397807 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7015426397807 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (23411112475247 / 50000000000000 : ℝ) ≤ Real.sqrt (7015426397807 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7015426397807 / 32000000000000 : ℝ) ≤ (9364444990099 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9364444990099 / 20000000000000 : ℝ) = (20000000000000 / 9364444990099 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23411112475247 / 50000000000000 : ℝ) = (3750000000000 / 23411112475247 : ℝ) := by norm_num
  have hL1 : (1238882586143 / 6250000000000 : ℝ) ≤ Real.log (1 + (7015426397807 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7015426397807 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-149229030036399 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9364444990099 / 20000000000000 : ℝ) ≤ (218951896381433 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113289253403203061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 9364444990099 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 9364444990099 : ℝ) = (9364444990099 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 23411112475247 : ℝ) ≤ (158831097600997 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113289253403203061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9364444990099 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23411112475247 / 50000000000000 : ℝ)) ≤ (158831097600997 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_260 : ∀ t : ℝ, (7015426397807 / 32000000000000 : ℝ) < t → t ≤ (14064972912701 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18831412410044822165552711 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (14064972912701 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_261
  have hV : (7200377358183543311689144662159943 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7015426397807 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_260 (Vfield_monotoneOn (show (7015426397807 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7015426397807 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_261 : (1441965475352155066248505698760231 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (14064972912701 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (14064972912701 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (4687912133999 / 10000000000000 : ℝ) ≤ Real.sqrt (14064972912701 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (14064972912701 / 64000000000000 : ℝ) ≤ (46879121339991 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (46879121339991 / 100000000000000 : ℝ) = (100000000000000 / 46879121339991 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4687912133999 / 10000000000000 : ℝ) = (750000000000 / 4687912133999 : ℝ) := by norm_num
  have hL1 : (2483229783123 / 12500000000000 : ℝ) ≤ Real.log (1 + (14064972912701 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((14064972912701 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-148992214798979 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (46879121339991 / 100000000000000 : ℝ) ≤ (438370348371299 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113242597842359761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 46879121339991 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 46879121339991 : ℝ) = (46879121339991 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (750000000000 / 4687912133999 : ℝ) ≤ (39660386748507 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113242597842359761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (46879121339991 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4687912133999 / 10000000000000 : ℝ)) ≤ (39660386748507 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_261 : ∀ t : ℝ, (14064972912701 / 64000000000000 : ℝ) < t → t ≤ (3524773257447 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-188123254242083024348399117 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3524773257447 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_262
  have hV : (1441965475352155066248505698760231 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (14064972912701 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_261 (Vfield_monotoneOn (show (14064972912701 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (14064972912701 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_262 : (7219267841068171735762943747177427 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (3524773257447 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3524773257447 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (23467974379483 / 50000000000000 : ℝ) ≤ Real.sqrt (3524773257447 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3524773257447 / 16000000000000 : ℝ) ≤ (46935948758967 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (46935948758967 / 100000000000000 : ℝ) = (100000000000000 / 46935948758967 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23467974379483 / 50000000000000 : ℝ) = (3750000000000 / 23467974379483 : ℝ) := by norm_num
  have hL1 : (1244346003023 / 6250000000000 : ℝ) ≤ Real.log (1 + (3524773257447 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3524773257447 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-148755959051429 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (46935948758967 / 100000000000000 : ℝ) ≤ (219418067393883 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113196019200713061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 46935948758967 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 46935948758967 : ℝ) = (46935948758967 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 23467974379483 : ℝ) ≤ (79226336722231 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113196019200713061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (46935948758967 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23467974379483 / 50000000000000 : ℝ)) ≤ (79226336722231 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_262 : ∀ t : ℝ, (3524773257447 / 16000000000000 : ℝ) < t → t ≤ (4522628207 / 20480000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-939669440627879297177369 / 500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4522628207 / 20480000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_263
  have hV : (7219267841068171735762943747177427 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3524773257447 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_262 (Vfield_monotoneOn (show (3524773257447 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3524773257447 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_263 : (7228698778751191554126845517076811 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (4522628207 / 20480000000 : ℝ) := by
  have hp : (0 : ℝ) < (4522628207 / 20480000000 : ℝ) := by norm_num
  have hs1 : (23496353728819 / 50000000000000 : ℝ) ≤ Real.sqrt (4522628207 / 20480000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4522628207 / 20480000000 : ℝ) ≤ (46992707457639 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (46992707457639 / 100000000000000 : ℝ) = (100000000000000 / 46992707457639 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23496353728819 / 50000000000000 : ℝ) = (3750000000000 / 23496353728819 : ℝ) := by norm_num
  have hL1 : (1995321474513 / 10000000000000 : ℝ) ≤ Real.log (1 + (4522628207 / 20480000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4522628207 / 20480000000 : ℝ) + (3 / 40) ^ 2) ≤ (-37130065039081 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (46992707457639 / 100000000000000 : ℝ) ≤ (439301154734213 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113149517206068361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 46992707457639 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 46992707457639 : ℝ) = (46992707457639 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 23496353728819 : ℝ) ≤ (39566118232749 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113149517206068361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (46992707457639 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23496353728819 / 50000000000000 : ℝ)) ≤ (39566118232749 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_263 : ∀ t : ℝ, (4522628207 / 20480000000 : ℝ) < t → t ≤ (7083666631981 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5867061852838602251975381 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7083666631981 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_264
  have hV : (7228698778751191554126845517076811 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4522628207 / 20480000000 : ℝ) := by norm_num
    refine le_trans V_pt_263 (Vfield_monotoneOn (show (4522628207 / 20480000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4522628207 / 20480000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_264 : (1447624043464623778569633291289199 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (7083666631981 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7083666631981 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (4704939768471 / 10000000000000 : ℝ) ≤ Real.sqrt (7083666631981 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7083666631981 / 32000000000000 : ℝ) ≤ (47049397684711 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (47049397684711 / 100000000000000 : ℝ) = (100000000000000 / 47049397684711 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4704939768471 / 10000000000000 : ℝ) = (250000000000 / 1568313256157 : ℝ) := by norm_num
  have hL1 : (3999374874387 / 20000000000000 : ℝ) ≤ Real.log (1 + (7083666631981 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7083666631981 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-37071278873711 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (47049397684711 / 100000000000000 : ℝ) ≤ (219882705458321 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113103091587825461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 47049397684711 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 47049397684711 : ℝ) = (47049397684711 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (250000000000 / 1568313256157 : ℝ) ≤ (79038470732847 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113103091587825461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (47049397684711 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4704939768471 / 10000000000000 : ℝ)) ≤ (79038470732847 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_264 : ∀ t : ℝ, (7083666631981 / 32000000000000 : ℝ) < t → t ≤ (14201453381049 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-37511896825425781870421869 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (14201453381049 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_265
  have hV : (1447624043464623778569633291289199 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7083666631981 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_264 (Vfield_monotoneOn (show (7083666631981 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7083666631981 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_265 : (14495064368333769925048838942338679 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (14201453381049 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (14201453381049 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (47106019687391 / 100000000000000 : ℝ) ≤ Real.sqrt (14201453381049 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (14201453381049 / 64000000000000 : ℝ) ≤ (1472063115231 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1472063115231 / 3125000000000 : ℝ) = (3125000000000 / 1472063115231 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (47106019687391 / 100000000000000 : ℝ) = (7500000000000 / 47106019687391 : ℝ) := by norm_num
  have hL1 : (20040514945429 / 100000000000000 : ℝ) ≤ Real.log (1 + (14201453381049 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((14201453381049 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-740252612333 / 500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1472063115231 / 3125000000000 : ℝ) ≤ (220114453012637 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113056742076962261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 1472063115231 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 1472063115231 : ℝ) = (1472063115231 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 47106019687391 : ℝ) ≤ (7894503754681 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113056742076962261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1472063115231 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (47106019687391 / 100000000000000 : ℝ)) ≤ (7894503754681 / 50000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_265 : ∀ t : ℝ, (14201453381049 / 64000000000000 : ℝ) < t → t ≤ (1779446687267 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18737436162268345525291693 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1779446687267 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_266
  have hV : (14495064368333769925048838942338679 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (14201453381049 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_265 (Vfield_monotoneOn (show (14201453381049 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (14201453381049 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_266 : (2902773882614091699529095957999089 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (1779446687267 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1779446687267 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (9432514742281 / 20000000000000 : ℝ) ≤ Real.sqrt (1779446687267 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1779446687267 / 8000000000000 : ℝ) ≤ (23581286855703 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (23581286855703 / 50000000000000 : ℝ) = (50000000000000 / 23581286855703 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9432514742281 / 20000000000000 : ℝ) = (1500000000000 / 9432514742281 : ℝ) := by norm_num
  have hL1 : (10042068241117 / 50000000000000 : ℝ) ≤ Real.log (1 + (1779446687267 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1779446687267 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7390823924473 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (23581286855703 / 50000000000000 : ℝ) ≤ (6885806917729 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (113010468406024061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 23581286855703 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 23581286855703 : ℝ) = (23581286855703 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 9432514742281 : ℝ) ≤ (63081547957 / 400000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (113010468406024061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (23581286855703 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9432514742281 / 20000000000000 : ℝ)) ≤ (63081547957 / 400000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_266 : ∀ t : ℝ, (1779446687267 / 8000000000000 : ℝ) < t → t ≤ (14269693615223 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-187190573142169951005071757 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (14269693615223 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_267
  have hV : (2902773882614091699529095957999089 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1779446687267 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_266 (Vfield_monotoneOn (show (1779446687267 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1779446687267 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_267 : (2906531124620817903734130255939569 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (14269693615223 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (14269693615223 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (9443812000201 / 20000000000000 : ℝ) ≤ Real.sqrt (14269693615223 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (14269693615223 / 64000000000000 : ℝ) ≤ (23609530000503 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (23609530000503 / 50000000000000 : ℝ) = (50000000000000 / 23609530000503 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9443812000201 / 20000000000000 : ℝ) = (1500000000000 / 9443812000201 : ℝ) := by norm_num
  have hL1 : (402554779979 / 2000000000000 : ℝ) ≤ Real.log (1 + (14269693615223 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((14269693615223 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-73791490499691 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (23609530000503 / 50000000000000 : ℝ) ≤ (44115362370381 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112964270309108661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 23609530000503 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 23609530000503 : ℝ) = (23609530000503 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 9443812000201 : ℝ) ≤ (78759160986181 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112964270309108661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (23609530000503 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9443812000201 / 20000000000000 : ℝ)) ≤ (78759160986181 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_267 : ∀ t : ℝ, (14269693615223 / 64000000000000 : ℝ) < t → t ≤ (1430381373231 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-37401616445672684212956621 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1430381373231 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_268
  have hV : (2906531124620817903734130255939569 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (14269693615223 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_267 (Vfield_monotoneOn (show (14269693615223 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (14269693615223 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_268 : (7275711526213218413597564672515117 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1430381373231 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1430381373231 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (23637739399493 / 50000000000000 : ℝ) ≤ Real.sqrt (1430381373231 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1430381373231 / 6400000000000 : ℝ) ≤ (47275478798987 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (47275478798987 / 100000000000000 : ℝ) = (100000000000000 / 47275478798987 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23637739399493 / 50000000000000 : ℝ) = (3750000000000 / 23637739399493 : ℝ) := by norm_num
  have hL1 : (20171322512157 / 100000000000000 : ℝ) ≤ Real.log (1 + (1430381373231 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1430381373231 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-230234417891 / 156250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (47275478798987 / 100000000000000 : ℝ) ≤ (441614851576359 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112918147521853761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 47275478798987 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 47275478798987 : ℝ) = (47275478798987 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 23637739399493 : ℝ) ≤ (78666713737601 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112918147521853761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (47275478798987 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23637739399493 / 50000000000000 : ℝ)) ≤ (78666713737601 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_268 : ∀ t : ℝ, (1430381373231 / 6400000000000 : ℝ) < t → t ≤ (14337933849397 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-93413427212417338910436399 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (14337933849397 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_269
  have hV : (7275711526213218413597564672515117 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1430381373231 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_268 (Vfield_monotoneOn (show (1430381373231 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1430381373231 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_269 : (7285085877386964551051469242498843 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (14337933849397 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (14337933849397 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (23665915173347 / 50000000000000 : ℝ) ≤ Real.sqrt (14337933849397 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (14337933849397 / 64000000000000 : ℝ) ≤ (9466366069339 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9466366069339 / 20000000000000 : ℝ) = (20000000000000 / 9466366069339 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23665915173347 / 50000000000000 : ℝ) = (3750000000000 / 23665915173347 : ℝ) := by norm_num
  have hL1 : (10107443519207 / 50000000000000 : ℝ) ≤ Real.log (1 + (14337933849397 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((14337933849397 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-147117615313663 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9466366069339 / 20000000000000 : ℝ) ≤ (55259416122579 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112872099781426461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 9466366069339 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 9466366069339 : ℝ) = (9466366069339 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 23665915173347 : ℝ) ≤ (157149182574651 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112872099781426461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9466366069339 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23665915173347 / 50000000000000 : ℝ)) ≤ (157149182574651 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_269 : ∀ t : ℝ, (14337933849397 / 64000000000000 : ℝ) < t → t ≤ (3593013491621 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-93323428558499968727300111 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3593013491621 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_270
  have hV : (7285085877386964551051469242498843 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (14337933849397 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_269 (Vfield_monotoneOn (show (14337933849397 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (14337933849397 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_270 : (14588901783630090256849917876312529 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3593013491621 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3593013491621 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (47388114884041 / 100000000000000 : ℝ) ≤ Real.sqrt (3593013491621 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3593013491621 / 16000000000000 : ℝ) ≤ (23694057442021 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (23694057442021 / 50000000000000 : ℝ) = (50000000000000 / 23694057442021 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (47388114884041 / 100000000000000 : ℝ) = (7500000000000 / 47388114884041 : ℝ) := by norm_num
  have hL1 : (10129216297127 / 50000000000000 : ℝ) ≤ Real.log (1 + (3593013491621 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3593013491621 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-36721435519717 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (23694057442021 / 50000000000000 : ℝ) ≤ (442535058529809 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112826126826508761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 23694057442021 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 23694057442021 : ℝ) = (23694057442021 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 47388114884041 : ℝ) ≤ (31393116695127 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112826126826508761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (23694057442021 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (47388114884041 / 100000000000000 : ℝ)) ≤ (31393116695127 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_270 : ∀ t : ℝ, (3593013491621 / 16000000000000 : ℝ) < t → t ≤ (14406174083571 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18646805938925244557108741 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (14406174083571 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_271
  have hV : (14588901783630090256849917876312529 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3593013491621 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_270 (Vfield_monotoneOn (show (3593013491621 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3593013491621 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_271 : (3651903298056813263682897456984451 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (14406174083571 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (14406174083571 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (11861083162379 / 25000000000000 : ℝ) ≤ Real.sqrt (14406174083571 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (14406174083571 / 64000000000000 : ℝ) ≤ (47444332649517 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (47444332649517 / 100000000000000 : ℝ) = (100000000000000 / 47444332649517 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (11861083162379 / 25000000000000 : ℝ) = (1875000000000 / 11861083162379 : ℝ) := by norm_num
  have hL1 : (10150979598097 / 50000000000000 : ℝ) ≤ Real.log (1 + (14406174083571 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((14406174083571 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-29330881050499 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (47444332649517 / 100000000000000 : ℝ) ≤ (110748510705511 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112780228397285261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 47444332649517 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 47444332649517 : ℝ) = (47444332649517 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 11861083162379 : ℝ) ≤ (156782626414049 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112780228397285261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (47444332649517 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (11861083162379 / 25000000000000 : ℝ)) ≤ (156782626414049 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_271 : ∀ t : ℝ, (14406174083571 / 64000000000000 : ℝ) < t → t ≤ (7220147100329 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-46572607974056334174573203 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7220147100329 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_272
  have hV : (3651903298056813263682897456984451 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (14406174083571 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_271 (Vfield_monotoneOn (show (14406174083571 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (14406174083571 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_272 : (3656576508386863150743195400732681 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (7220147100329 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7220147100329 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (11875120970049 / 25000000000000 : ℝ) ≤ Real.sqrt (7220147100329 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7220147100329 / 32000000000000 : ℝ) ≤ (47500483880197 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (47500483880197 / 100000000000000 : ℝ) = (100000000000000 / 47500483880197 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (11875120970049 / 25000000000000 : ℝ) = (625000000000 / 3958373656683 : ℝ) := by norm_num
  have hL1 : (813818674429 / 4000000000000 : ℝ) ≤ Real.log (1 + (7220147100329 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7220147100329 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2928472047169 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (47500483880197 / 100000000000000 : ℝ) ≤ (443452284440573 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112734404235432361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 47500483880197 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 47500483880197 : ℝ) = (47500483880197 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (625000000000 / 3958373656683 : ℝ) ≤ (156600307656437 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112734404235432361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (47500483880197 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (11875120970049 / 25000000000000 : ℝ)) ≤ (156600307656437 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_272 : ∀ t : ℝ, (7220147100329 / 32000000000000 : ℝ) < t → t ≤ (2894882863549 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-46528486686626985518044219 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2894882863549 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_273
  have hV : (3656576508386863150743195400732681 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7220147100329 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_272 (Vfield_monotoneOn (show (7220147100329 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7220147100329 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_273 : (14644980360324928760908395203057671 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2894882863549 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2894882863549 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (47556568811759 / 100000000000000 : ℝ) ≤ Real.sqrt (2894882863549 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2894882863549 / 12800000000000 : ℝ) ≤ (594457110147 / 1250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (594457110147 / 1250000000000 : ℝ) = (1250000000000 / 594457110147 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (47556568811759 / 100000000000000 : ℝ) = (7500000000000 / 47556568811759 : ℝ) := by norm_num
  have hL1 : (127430972527 / 625000000000 : ℝ) ≤ Real.log (1 + (2894882863549 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2894882863549 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-146193330937743 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (594457110147 / 1250000000000 : ℝ) ≤ (110977446488463 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112688654084104461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1250000000000 / 594457110147 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (1250000000000 / 594457110147 : ℝ) = (594457110147 / 1250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 47556568811759 : ℝ) ≤ (31283724699933 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112688654084104461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (594457110147 / 1250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (47556568811759 / 100000000000000 : ℝ)) ≤ (31283724699933 / 200000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_273 : ∀ t : ℝ, (2894882863549 / 12800000000000 : ℝ) < t → t ≤ (906783402177 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-92969288698682375485012097 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (906783402177 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_274
  have hV : (14644980360324928760908395203057671 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2894882863549 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_273 (Vfield_monotoneOn (show (2894882863549 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2894882863549 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_274 : (458238632032736627845913246753857 / 156250000000000000000000000000000 : ℝ) ≤ Vfield (906783402177 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (906783402177 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (1487893364953 / 3125000000000 : ℝ) ≤ Real.sqrt (906783402177 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (906783402177 / 4000000000000 : ℝ) ≤ (47612587678497 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (47612587678497 / 100000000000000 : ℝ) = (100000000000000 / 47612587678497 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1487893364953 / 3125000000000 : ℝ) = (234375000000 / 1487893364953 : ℝ) := by norm_num
  have hL1 : (20432425443427 / 100000000000000 : ℝ) ≤ Real.log (1 + (906783402177 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((906783402177 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-72981794274167 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (47612587678497 / 100000000000000 : ℝ) ≤ (111091637478919 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112642977687922061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 47612587678497 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 47612587678497 : ℝ) = (47612587678497 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (234375000000 / 1487893364953 : ℝ) ≤ (78118785135303 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112642977687922061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (47612587678497 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1487893364953 / 3125000000000 : ℝ)) ≤ (78118785135303 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_274 : ∀ t : ℝ, (906783402177 / 4000000000000 : ℝ) < t → t ≤ (14542654551919 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-185764298559211686579194729 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (14542654551919 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_275
  have hV : (458238632032736627845913246753857 / 156250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (906783402177 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_274 (Vfield_monotoneOn (show (906783402177 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (906783402177 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_275 : (7341136839978531389003440189485771 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (14542654551919 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (14542654551919 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (23834270356659 / 50000000000000 : ℝ) ≤ Real.sqrt (14542654551919 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (14542654551919 / 64000000000000 : ℝ) ≤ (47668540713319 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (47668540713319 / 100000000000000 : ℝ) = (100000000000000 / 47668540713319 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23834270356659 / 50000000000000 : ℝ) = (1250000000000 / 7944756785553 : ℝ) := by norm_num
  have hL1 : (819035055779 / 4000000000000 : ℝ) ≤ Real.log (1 + (14542654551919 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((14542654551919 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-145734372764973 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (47668540713319 / 100000000000000 : ℝ) ≤ (444822578865267 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112597374792962961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 47668540713319 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 47668540713319 : ℝ) = (47668540713319 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 7944756785553 : ℝ) ≤ (156057144325839 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112597374792962961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (47668540713319 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23834270356659 / 50000000000000 : ℝ)) ≤ (156057144325839 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_275 : ∀ t : ℝ, (14542654551919 / 64000000000000 : ℝ) < t → t ≤ (7288387334503 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-579972144089871917652421 / 312500000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7288387334503 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_276
  have hV : (7341136839978531389003440189485771 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (14542654551919 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_275 (Vfield_monotoneOn (show (14542654551919 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (14542654551919 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_276 : (588035711082133735962447346460559 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (7288387334503 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7288387334503 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (1908977125911 / 4000000000000 : ℝ) ≤ Real.sqrt (7288387334503 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7288387334503 / 32000000000000 : ℝ) ≤ (745694189809 / 1562500000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (745694189809 / 1562500000000 : ℝ) = (1562500000000 / 745694189809 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1908977125911 / 4000000000000 : ℝ) = (100000000000 / 636325708637 : ℝ) := by norm_num
  have hL1 : (1282456779617 / 6250000000000 : ℝ) ≤ Real.log (1 + (7288387334503 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7288387334503 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-145505681179051 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (745694189809 / 1562500000000 : ℝ) ≤ (445277875327447 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112551845146744961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1562500000000 / 745694189809 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (1562500000000 / 745694189809 : ℝ) = (745694189809 / 1562500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (100000000000 / 636325708637 : ℝ) ≤ (3896933551283 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112551845146744961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (745694189809 / 1562500000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1908977125911 / 4000000000000 : ℝ)) ≤ (3896933551283 / 25000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_276 : ∀ t : ℝ, (7288387334503 / 32000000000000 : ℝ) < t → t ≤ (732250745159 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-185247769241339503829013439 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (732250745159 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_277
  have hV : (588035711082133735962447346460559 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7288387334503 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_276 (Vfield_monotoneOn (show (7288387334503 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7288387334503 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_277 : (14738076104592597284919495047416149 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (732250745159 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (732250745159 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (47836007135021 / 100000000000000 : ℝ) ≤ Real.sqrt (732250745159 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (732250745159 / 3200000000000 : ℝ) ≤ (23918003567511 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (23918003567511 / 50000000000000 : ℝ) = (50000000000000 / 23918003567511 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (47836007135021 / 100000000000000 : ℝ) = (7500000000000 / 47836007135021 : ℝ) := by norm_num
  have hL1 : (20606116083231 / 100000000000000 : ℝ) ≤ Real.log (1 + (732250745159 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((732250745159 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-145049861047373 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (23918003567511 / 50000000000000 : ℝ) ≤ (446186280817303 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112461004597759361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 23918003567511 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 23918003567511 : ℝ) = (23918003567511 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 47836007135021 : ℝ) ≤ (77759797101009 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112461004597759361923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (23918003567511 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (47836007135021 / 100000000000000 : ℝ)) ≤ (77759797101009 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_277 : ∀ t : ℝ, (732250745159 / 3200000000000 : ℝ) < t → t ≤ (7356627568677 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9245422714706711352624849 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7356627568677 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_278
  have hV : (14738076104592597284919495047416149 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (732250745159 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_277 (Vfield_monotoneOn (show (732250745159 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (732250745159 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_278 : (3693796654711914097524127933441977 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (7356627568677 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7356627568677 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (11986831616433 / 25000000000000 : ℝ) ≤ Real.sqrt (7356627568677 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7356627568677 / 32000000000000 : ℝ) ≤ (47947326465733 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (47947326465733 / 100000000000000 : ℝ) = (100000000000000 / 47947326465733 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (11986831616433 / 25000000000000 : ℝ) = (625000000000 / 3995610538811 : ℝ) := by norm_num
  have hL1 : (5173212100583 / 25000000000000 : ℝ) ≤ Real.log (1 + (7356627568677 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7356627568677 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-36149027302869 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (47947326465733 / 100000000000000 : ℝ) ≤ (447091786299447 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112370454049544961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 47947326465733 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 47947326465733 : ℝ) = (47947326465733 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (625000000000 / 3995610538811 : ℝ) ≤ (6206571935469 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112370454049544961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (47947326465733 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (11986831616433 / 25000000000000 : ℝ)) ≤ (6206571935469 / 40000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_278 : ∀ t : ℝ, (7356627568677 / 32000000000000 : ℝ) < t → t ≤ (1847686921441 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-184572983018958491402188563 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1847686921441 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_279
  have hV : (3693796654711914097524127933441977 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7356627568677 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_278 (Vfield_monotoneOn (show (7356627568677 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7356627568677 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_279 : (7406112363601711989505752602503739 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1847686921441 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1847686921441 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (24029193972131 / 50000000000000 : ℝ) ≤ Real.sqrt (1847686921441 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1847686921441 / 8000000000000 : ℝ) ≤ (48058387944263 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (48058387944263 / 100000000000000 : ℝ) = (100000000000000 / 48058387944263 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (24029193972131 / 50000000000000 : ℝ) = (3750000000000 / 24029193972131 : ℝ) := by norm_num
  have hL1 : (324679774401 / 1562500000000 : ℝ) ≤ Real.log (1 + (1847686921441 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1847686921441 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-144144406986219 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (48058387944263 / 100000000000000 : ℝ) ≤ (447994411464469 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (112280191533042761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 48058387944263 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 48058387944263 : ℝ) = (48058387944263 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (3750000000000 / 24029193972131 : ℝ) ≤ (19351428340079 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (112280191533042761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (48058387944263 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (24029193972131 / 50000000000000 : ℝ)) ≤ (19351428340079 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_279 : ∀ t : ℝ, (1847686921441 / 8000000000000 : ℝ) < t → t ≤ (7424867802851 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-92120604853362948950182029 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7424867802851 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_280
  have hV : (7406112363601711989505752602503739 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1847686921441 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_279 (Vfield_monotoneOn (show (1847686921441 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1847686921441 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
