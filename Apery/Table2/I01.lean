import Apery.Table2.U01
import Apery.Table2.U02

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_40 : (4909840345778634009983107728551807 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3068199571 / 200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3068199571 / 200000000000 : ℝ) := by norm_num
  have hs1 : (12385878190503 / 100000000000000 : ℝ) ≤ Real.sqrt (3068199571 / 200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3068199571 / 200000000000 : ℝ) ≤ (1548234773813 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1548234773813 / 12500000000000 : ℝ) = (12500000000000 / 1548234773813 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (12385878190503 / 100000000000000 : ℝ) = (2500000000000 / 4128626063501 : ℝ) := by norm_num
  have hL1 : (1522451455017 / 100000000000000 : ℝ) ≤ Real.log (1 + (3068199571 / 200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3068199571 / 200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-193242665085029 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1548234773813 / 12500000000000 : ℝ) ≤ (61615588138741 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (144756515051741461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 1548234773813 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 1548234773813 : ℝ) = (1548234773813 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (125000000000000000000000 / 447758638822193041629853 : ℝ) ≤ (136118632090209 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2500000000000 / 4128626063501 : ℝ) ≤ (136118632090209 / 250000000000000 : ℝ) := by
    have hw : (58452214353 / 50000000000 : ℝ) ≤ Real.sqrt (1 + (2500000000000 / 4128626063501 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2500000000000 / 4128626063501 : ℝ) / (1 + (58452214353 / 50000000000 : ℝ)) = (125000000000000000000000 / 447758638822193041629853 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (144756515051741461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1548234773813 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (12385878190503 / 100000000000000 : ℝ)) ≤ (136118632090209 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_40 : ∀ t : ℝ, (3068199571 / 200000000000 : ℝ) < t → t ≤ (255845148549 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-283425813910016345599748471 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (255845148549 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_41
  have hV : (4909840345778634009983107728551807 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3068199571 / 200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_40 (Vfield_monotoneOn (show (3068199571 / 200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3068199571 / 200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_41 : (2472411811160671496270397026766771 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (255845148549 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (255845148549 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (6322642205659 / 50000000000000 : ℝ) ≤ Real.sqrt (255845148549 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (255845148549 / 16000000000000 : ℝ) ≤ (12645284411319 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (12645284411319 / 100000000000000 : ℝ) = (100000000000000 / 12645284411319 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6322642205659 / 50000000000000 : ℝ) = (3750000000000 / 6322642205659 : ℝ) := by norm_num
  have hL1 : (1586382330807 / 100000000000000 : ℝ) ≤ Real.log (1 + (255845148549 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((255845148549 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-76687057446601 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (12645284411319 / 100000000000000 : ℝ) ≤ (125785230493909 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (144501109630098761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 12645284411319 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 12645284411319 : ℝ) = (12645284411319 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (5859375000000000000000000 / 21365183219411582836289719 : ℝ) ≤ (267667654781053 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3750000000000 / 6322642205659 : ℝ) ≤ (267667654781053 / 500000000000000 : ℝ) := by
    have hw : (1816654240341 / 1562500000000 : ℝ) ≤ Real.sqrt (1 + (3750000000000 / 6322642205659 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3750000000000 / 6322642205659 : ℝ) / (1 + (1816654240341 / 1562500000000 : ℝ)) = (5859375000000000000000000 / 21365183219411582836289719 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (144501109630098761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (12645284411319 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6322642205659 / 50000000000000 : ℝ)) ≤ (267667654781053 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_41 : ∀ t : ℝ, (255845148549 / 16000000000000 : ℝ) < t → t ≤ (133117165709 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-70707002277321411606398859 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (133117165709 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_42
  have hV : (2472411811160671496270397026766771 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (255845148549 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_41 (Vfield_monotoneOn (show (255845148549 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (255845148549 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_42 : (124509966112095297247522349816507 / 125000000000000000000000000000000 : ℝ) ≤ Vfield (133117165709 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (133117165709 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (322486876803 / 2500000000000 : ℝ) ≤ Real.sqrt (133117165709 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (133117165709 / 8000000000000 : ℝ) ≤ (12899475072121 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (12899475072121 / 100000000000000 : ℝ) = (100000000000000 / 12899475072121 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (322486876803 / 2500000000000 : ℝ) = (62500000000 / 107495625601 : ℝ) := by norm_num
  have hL1 : (1650272361141 / 100000000000000 : ℝ) ≤ Real.log (1 + (133117165709 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((133117165709 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-190237762551559 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (12899475072121 / 100000000000000 : ℝ) ≤ (12828633441201 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (144250999238288661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 12899475072121 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 12899475072121 : ℝ) = (12899475072121 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (6250000000000000000000000 / 23184014507552361509509827 : ℝ) ≤ (32915309590933 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (62500000000 / 107495625601 : ℝ) ≤ (32915309590933 / 62500000000000 : ℝ) := by
    have hw : (115674027458627 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (62500000000 / 107495625601 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (62500000000 / 107495625601 : ℝ) / (1 + (115674027458627 / 100000000000000 : ℝ)) = (6250000000000000000000000 / 23184014507552361509509827 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (144250999238288661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (12899475072121 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (322486876803 / 2500000000000 : ℝ)) ≤ (32915309590933 / 62500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_42 : ∀ t : ℝ, (133117165709 / 8000000000000 : ℝ) < t → t ≤ (108571569141 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-141292837427791336106519573 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (108571569141 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_43
  have hV : (124509966112095297247522349816507 / 125000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (133117165709 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_42 (Vfield_monotoneOn (show (133117165709 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (133117165709 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_43 : (4998385069771066655656007936605471 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (108571569141 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (108571569141 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (13024710237959 / 100000000000000 : ℝ) ≤ Real.sqrt (108571569141 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (108571569141 / 6400000000000 : ℝ) ≤ (325617755949 / 2500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (325617755949 / 2500000000000 : ℝ) = (2500000000000 / 325617755949 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13024710237959 / 100000000000000 : ℝ) = (7500000000000 / 13024710237959 : ℝ) := by norm_num
  have hL1 : (420550518891 / 25000000000000 : ℝ) ≤ Real.log (1 + (108571569141 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((108571569141 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-379027859467729 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (325617755949 / 2500000000000 : ℝ) ≤ (16189749014863 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (144127833467599261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2500000000000 / 325617755949 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2500000000000 / 325617755949 : ℝ) = (325617755949 / 2500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (375000000000000000000000000 / 1402722499115282315264507647 : ℝ) ≤ (261228366789493 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 13024710237959 : ℝ) ≤ (261228366789493 / 500000000000000 : ℝ) := by
    have hw : (57697021545033 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (7500000000000 / 13024710237959 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7500000000000 / 13024710237959 : ℝ) / (1 + (57697021545033 / 50000000000000 : ℝ)) = (375000000000000000000000000 / 1402722499115282315264507647 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (144127833467599261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (325617755949 / 2500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13024710237959 / 100000000000000 : ℝ)) ≤ (261228366789493 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_43 : ∀ t : ℝ, (108571569141 / 6400000000000 : ℝ) < t → t ≤ (276623514287 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-141183250559293991937026527 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (276623514287 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_44
  have hV : (4998385069771066655656007936605471 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (108571569141 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_43 (Vfield_monotoneOn (show (108571569141 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (108571569141 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_44 : (5016492997357700001477867222864203 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (276623514287 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (276623514287 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (13148752656787 / 100000000000000 : ℝ) ≤ Real.sqrt (276623514287 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (276623514287 / 16000000000000 : ℝ) ≤ (3287188164197 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3287188164197 / 25000000000000 : ℝ) = (25000000000000 / 3287188164197 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13148752656787 / 100000000000000 : ℝ) = (7500000000000 / 13148752656787 : ℝ) := by norm_num
  have hL1 : (53566299943 / 3125000000000 : ℝ) ≤ Real.log (1 + (276623514287 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((276623514287 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-94400213119447 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3287188164197 / 25000000000000 : ℝ) ≤ (65368765022531 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (144005879674983461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 3287188164197 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 3287188164197 : ℝ) = (3287188164197 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000000000000000000 / 2828611360344351149573965663 : ℝ) ≤ (51836760211661 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 13148752656787 : ℝ) ≤ (51836760211661 / 100000000000000 : ℝ) := by
    have hw : (115123931081349 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7500000000000 / 13148752656787 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7500000000000 / 13148752656787 : ℝ) / (1 + (115123931081349 / 100000000000000 : ℝ)) = (750000000000000000000000000 / 2828611360344351149573965663 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (144005879674983461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3287188164197 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13148752656787 / 100000000000000 : ℝ)) ≤ (51836760211661 / 100000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_44 : ∀ t : ℝ, (276623514287 / 16000000000000 : ℝ) < t → t ≤ (563636211443 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-70541294803348096810597413 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (563636211443 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_45
  have hV : (5016492997357700001477867222864203 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (276623514287 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_44 (Vfield_monotoneOn (show (276623514287 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (276623514287 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_45 : (2517357371012316598328156066002797 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (563636211443 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (563636211443 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (6635817886213 / 50000000000000 : ℝ) ≤ Real.sqrt (563636211443 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (563636211443 / 32000000000000 : ℝ) ≤ (13271635772427 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13271635772427 / 100000000000000 : ℝ) = (100000000000000 / 13271635772427 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6635817886213 / 50000000000000 : ℝ) = (3750000000000 / 6635817886213 : ℝ) := by norm_num
  have hL1 : (1746030935479 / 100000000000000 : ℝ) ≤ Real.log (1 + (563636211443 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((563636211443 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-376193922808479 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13271635772427 / 100000000000000 : ℝ) ≤ (26389056925507 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (143885104216736161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 13271635772427 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 13271635772427 : ℝ) = (13271635772427 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (187500000000000000000000000 / 712896453896781879330538891 : ℝ) ≤ (32148355230991 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3750000000000 / 6635817886213 : ℝ) ≤ (32148355230991 / 62500000000000 : ℝ) := by
    have hw : (57431588105807 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (3750000000000 / 6635817886213 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3750000000000 / 6635817886213 : ℝ) / (1 + (57431588105807 / 50000000000000 : ℝ)) = (187500000000000000000000000 / 712896453896781879330538891 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (143885104216736161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13271635772427 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6635817886213 / 50000000000000 : ℝ)) ≤ (32148355230991 / 62500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_45 : ∀ t : ℝ, (563636211443 / 32000000000000 : ℝ) < t → t ≤ (71753174289 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-35247276873896200600710843 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (71753174289 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_46
  have hV : (2517357371012316598328156066002797 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (563636211443 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_45 (Vfield_monotoneOn (show (563636211443 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (563636211443 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_46 : (631630386077912408950196061984969 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (71753174289 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (71753174289 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (1674173936801 / 12500000000000 : ℝ) ≤ Real.sqrt (71753174289 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (71753174289 / 4000000000000 : ℝ) ≤ (13393391494409 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13393391494409 / 100000000000000 : ℝ) = (100000000000000 / 13393391494409 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1674173936801 / 12500000000000 : ℝ) = (937500000000 / 1674173936801 : ℝ) := by norm_num
  have hL1 : (444482523493 / 25000000000000 : ℝ) ≤ Real.log (1 + (71753174289 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((71753174289 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46850814166531 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13393391494409 / 100000000000000 : ℝ) ≤ (16642697113307 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (143765474988844061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 13393391494409 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 13393391494409 : ℝ) = (13393391494409 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (31250000000000000000000000 / 119765547568574725972653809 : ℝ) ≤ (255235656717789 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (937500000000 / 1674173936801 : ℝ) ≤ (255235656717789 / 500000000000000 : ℝ) := by
    have hw : (114611298627827 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (937500000000 / 1674173936801 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (937500000000 / 1674173936801 : ℝ) / (1 + (114611298627827 / 100000000000000 : ℝ)) = (31250000000000000000000000 / 119765547568574725972653809 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (143765474988844061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13393391494409 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1674173936801 / 12500000000000 : ℝ)) ≤ (255235656717789 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_46 : ∀ t : ℝ, (71753174289 / 4000000000000 : ℝ) < t → t ≤ (584414577181 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-281803155897871266830267521 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (584414577181 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_47
  have hV : (631630386077912408950196061984969 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (71753174289 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_46 (Vfield_monotoneOn (show (71753174289 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (71753174289 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_47 : (5071471257658434495181872870798519 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (584414577181 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (584414577181 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (13514050294751 / 100000000000000 : ℝ) ≤ Real.sqrt (584414577181 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (584414577181 / 32000000000000 : ℝ) ≤ (422314071711 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (422314071711 / 3125000000000 : ℝ) = (3125000000000 / 422314071711 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13514050294751 / 100000000000000 : ℝ) = (7500000000000 / 13514050294751 : ℝ) := by norm_num
  have hL1 : (904909540073 / 50000000000000 : ℝ) ≤ Real.log (1 + (584414577181 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((584414577181 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1166994030607 / 312500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (422314071711 / 3125000000000 : ℝ) ≤ (33581678373809 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (143646961329966061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 422314071711 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 422314071711 : ℝ) = (422314071711 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (250000000000000000000000000 / 965659305994324509446502037 : ℝ) ≤ (5066570223633 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 13514050294751 : ℝ) ≤ (5066570223633 / 10000000000000 : ℝ) := by
    have hw : (114367850851361 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7500000000000 / 13514050294751 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7500000000000 / 13514050294751 : ℝ) / (1 + (114367850851361 / 100000000000000 : ℝ)) = (250000000000000000000000000 / 965659305994324509446502037 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (143646961329966061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (422314071711 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13514050294751 / 100000000000000 : ℝ)) ≤ (5066570223633 / 10000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_47 : ∀ t : ℝ, (584414577181 / 32000000000000 : ℝ) < t → t ≤ (11896075201 / 640000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-8801193661305882007701887 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11896075201 / 640000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_48
  have hV : (5071471257658434495181872870798519 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (584414577181 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_47 (Vfield_monotoneOn (show (584414577181 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (584414577181 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_48 : (5089992873862650971511312392807997 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (11896075201 / 640000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11896075201 / 640000000000 : ℝ) := by norm_num
  have hs1 : (13633641297013 / 100000000000000 : ℝ) ≤ Real.sqrt (11896075201 / 640000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11896075201 / 640000000000 : ℝ) ≤ (6816820648507 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6816820648507 / 50000000000000 : ℝ) = (50000000000000 / 6816820648507 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13633641297013 / 100000000000000 : ℝ) = (7500000000000 / 13633641297013 : ℝ) := by norm_num
  have hL1 : (230212237561 / 12500000000000 : ℝ) ≤ Real.log (1 + (11896075201 / 640000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11896075201 / 640000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-372088139577133 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6816820648507 / 50000000000000 : ℝ) ≤ (8468811717087 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (143529533932150461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 6816820648507 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 6816820648507 : ℝ) = (6816820648507 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (250000000000000000000000000 / 973134845774833539189681621 : ℝ) ≤ (31432970253641 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 13633641297013 : ℝ) ≤ (31432970253641 / 62500000000000 : ℝ) := by
    have hw : (114132415084451 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7500000000000 / 13633641297013 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7500000000000 / 13633641297013 : ℝ) / (1 + (114132415084451 / 100000000000000 : ℝ)) = (250000000000000000000000000 / 973134845774833539189681621 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (143529533932150461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6816820648507 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13633641297013 / 100000000000000 : ℝ)) ≤ (31432970253641 / 62500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_48 : ∀ t : ℝ, (11896075201 / 640000000000 : ℝ) < t → t ≤ (605192942919 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-281481961700314809085734491 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (605192942919 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_49
  have hV : (5089992873862650971511312392807997 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11896075201 / 640000000000 : ℝ) := by norm_num
    refine le_trans V_pt_48 (Vfield_monotoneOn (show (11896075201 / 640000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11896075201 / 640000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_49 : (510860193746986863775091904875191 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (605192942919 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (605192942919 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (1375219235839 / 10000000000000 : ℝ) ≤ Real.sqrt (605192942919 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (605192942919 / 32000000000000 : ℝ) ≤ (13752192358391 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13752192358391 / 100000000000000 : ℝ) = (100000000000000 / 13752192358391 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1375219235839 / 10000000000000 : ℝ) = (750000000000 / 1375219235839 : ℝ) := by norm_num
  have hL1 : (1873566561477 / 100000000000000 : ℝ) ≤ Real.log (1 + (605192942919 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((605192942919 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-370756170548253 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13752192358391 / 100000000000000 : ℝ) ≤ (136664679209671 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (143413164758522561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 13752192358391 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 13752192358391 : ℝ) = (13752192358391 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (25000000000000000000000000 / 98055240543235833725168279 : ℝ) ≤ (6240996279977 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (750000000000 / 1375219235839 : ℝ) ≤ (6240996279977 / 12500000000000 : ℝ) := by
    have hw : (113904600781883 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (750000000000 / 1375219235839 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (750000000000 / 1375219235839 : ℝ) / (1 + (113904600781883 / 100000000000000 : ℝ)) = (25000000000000000000000000 / 98055240543235833725168279 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (143413164758522561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13752192358391 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1375219235839 / 10000000000000 : ℝ)) ≤ (6240996279977 / 12500000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_49 : ∀ t : ℝ, (605192942919 / 32000000000000 : ℝ) < t → t ≤ (153895531447 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-70333342055498682210253927 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (153895531447 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_50
  have hV : (510860193746986863775091904875191 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (605192942919 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_49 (Vfield_monotoneOn (show (605192942919 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (605192942919 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_50 : (5127292797910921674447220597017579 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (153895531447 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (153895531447 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (13869730145491 / 100000000000000 : ℝ) ≤ Real.sqrt (153895531447 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (153895531447 / 8000000000000 : ℝ) ≤ (3467432536373 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3467432536373 / 25000000000000 : ℝ) = (25000000000000 / 3467432536373 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13869730145491 / 100000000000000 : ℝ) = (7500000000000 / 13869730145491 : ℝ) := by norm_num
  have hL1 : (381085013917 / 20000000000000 : ℝ) ≤ Real.log (1 + (153895531447 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((153895531447 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46180213747807 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3467432536373 / 25000000000000 : ℝ) ≤ (137818057121817 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (143297826967307961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 3467432536373 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 3467432536373 : ℝ) = (3467432536373 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000000000000000000 / 2963740005289144349876839121 : ℝ) ≤ (247855300151679 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 13869730145491 : ℝ) ≤ (247855300151679 / 500000000000000 : ℝ) := by
    have hw : (113684042457931 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7500000000000 / 13869730145491 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7500000000000 / 13869730145491 : ℝ) / (1 + (113684042457931 / 100000000000000 : ℝ)) = (750000000000000000000000000 / 2963740005289144349876839121 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (143297826967307961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3467432536373 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13869730145491 / 100000000000000 : ℝ)) ≤ (247855300151679 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_50 : ∀ t : ℝ, (153895531447 / 8000000000000 : ℝ) < t → t ≤ (318180245763 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-11242231536798916978601543 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (318180245763 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_51
  have hV : (5127292797910921674447220597017579 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (153895531447 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_50 (Vfield_monotoneOn (show (153895531447 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (153895531447 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_51 : (5164898910262890495731699503532217 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (318180245763 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (318180245763 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (14101867025393 / 100000000000000 : ℝ) ≤ Real.sqrt (318180245763 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (318180245763 / 16000000000000 : ℝ) ≤ (7050933512697 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7050933512697 / 50000000000000 : ℝ) = (50000000000000 / 7050933512697 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14101867025393 / 100000000000000 : ℝ) = (7500000000000 / 14101867025393 : ℝ) := by norm_num
  have hL1 : (61534739157 / 3125000000000 : ℝ) ≤ Real.log (1 + (318180245763 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((318180245763 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-366863514398273 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7050933512697 / 50000000000000 : ℝ) ≤ (140094889551199 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (143070143724369761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 7050933512697 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 7050933512697 : ℝ) = (7050933512697 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (250000000000000000000000000 / 1002470445989155542962067393 : ℝ) ≤ (122199365099867 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 14101867025393 : ℝ) ≤ (122199365099867 / 250000000000000 : ℝ) := by
    have hw : (113263345382003 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7500000000000 / 14101867025393 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7500000000000 / 14101867025393 : ℝ) / (1 + (113263345382003 / 100000000000000 : ℝ)) = (250000000000000000000000000 / 1002470445989155542962067393 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (143070143724369761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7050933512697 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14101867025393 / 100000000000000 : ℝ)) ≤ (122199365099867 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_51 : ∀ t : ℝ, (318180245763 / 16000000000000 : ℝ) < t → t ≤ (41071178579 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-28080017513087460990253833 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (41071178579 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_52
  have hV : (5164898910262890495731699503532217 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (318180245763 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_51 (Vfield_monotoneOn (show (318180245763 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (318180245763 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_52 : (5202772121713861153234038667966647 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (41071178579 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (41071178579 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (14330243992863 / 100000000000000 : ℝ) ≤ Real.sqrt (41071178579 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (41071178579 / 2000000000000 : ℝ) ≤ (447820124777 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (447820124777 / 3125000000000 : ℝ) = (3125000000000 / 447820124777 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14330243992863 / 100000000000000 : ℝ) = (2500000000000 / 4776747997621 : ℝ) := by norm_num
  have hL1 : (508189425617 / 25000000000000 : ℝ) ≤ Real.log (1 + (41071178579 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((41071178579 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-182175061236507 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (447820124777 / 3125000000000 : ℝ) ≤ (71166709251457 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (142846290829198261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 447820124777 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 447820124777 : ℝ) = (447820124777 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (250000000000000000000000000 / 1016815981947027177306126859 : ℝ) ≤ (120541813738707 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2500000000000 / 4776747997621 : ℝ) ≤ (120541813738707 / 250000000000000 : ℝ) := by
    have hw : (112867830258879 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (2500000000000 / 4776747997621 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2500000000000 / 4776747997621 : ℝ) / (1 + (112867830258879 / 100000000000000 : ℝ)) = (250000000000000000000000000 / 1016815981947027177306126859 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (142846290829198261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (447820124777 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14330243992863 / 100000000000000 : ℝ)) ≤ (120541813738707 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_52 : ∀ t : ℝ, (41071178579 / 2000000000000 : ℝ) < t → t ≤ (34934779437 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-14017042139494650544526683 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (34934779437 / 1600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_53
  have hV : (5202772121713861153234038667966647 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (41071178579 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_52 (Vfield_monotoneOn (show (41071178579 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (41071178579 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_53 : (5279184118549556596353577901991243 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (34934779437 / 1600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (34934779437 / 1600000000000 : ℝ) := by norm_num
  have hs1 : (14776412672947 / 100000000000000 : ℝ) ≤ Real.sqrt (34934779437 / 1600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (34934779437 / 1600000000000 : ℝ) ≤ (3694103168237 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3694103168237 / 25000000000000 : ℝ) = (25000000000000 / 3694103168237 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14776412672947 / 100000000000000 : ℝ) = (7500000000000 / 14776412672947 : ℝ) := by norm_num
  have hL1 : (539982101381 / 25000000000000 : ℝ) ≤ Real.log (1 + (34934779437 / 1600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((34934779437 / 1600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-359505265794467 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3694103168237 / 25000000000000 : ℝ) ≤ (29340512101341 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (142409376628819161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 3694103168237 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 3694103168237 : ℝ) = (3694103168237 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (187500000000000000000000000 / 783681040114336118403612347 : ℝ) ≤ (117420455317521 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7500000000000 / 14776412672947 : ℝ) ≤ (117420455317521 / 250000000000000 : ℝ) := by
    have hw : (28035947050201 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (7500000000000 / 14776412672947 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7500000000000 / 14776412672947 : ℝ) / (1 + (28035947050201 / 25000000000000 : ℝ)) = (187500000000000000000000000 / 783681040114336118403612347 : ℝ) := by norm_num
    rw [e] at this; linarith [hA6]
  have hA1' : (142409376628819161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3694103168237 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14776412672947 / 100000000000000 : ℝ)) ≤ (117420455317521 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_53 : ∀ t : ℝ, (34934779437 / 1600000000000 : ℝ) < t → t ≤ (92531540027 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-279935218218960902877269273 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (92531540027 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_54
  have hV : (5279184118549556596353577901991243 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (34934779437 / 1600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_53 (Vfield_monotoneOn (show (34934779437 / 1600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (34934779437 / 1600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_54 : (669536460042516256253681081436951 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (92531540027 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (92531540027 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (1901187334879 / 12500000000000 : ℝ) ≤ Real.sqrt (92531540027 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (92531540027 / 4000000000000 : ℝ) ≤ (15209498679033 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (15209498679033 / 100000000000000 : ℝ) = (100000000000000 / 15209498679033 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1901187334879 / 12500000000000 : ℝ) = (937500000000 / 1901187334879 : ℝ) := by norm_num
  have hL1 : (457387518017 / 20000000000000 : ℝ) ≤ Real.log (1 + (92531540027 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((92531540027 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-70976865733549 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (15209498679033 / 100000000000000 : ℝ) ≤ (150938202084497 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (141985812471039961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 15209498679033 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 15209498679033 : ℝ) = (15209498679033 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (937500000000 / 1901187334879 : ℝ) ≤ (458122764937519 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (141985812471039961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (15209498679033 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1901187334879 / 12500000000000 : ℝ)) ≤ (458122764937519 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_54 : ∀ t : ℝ, (92531540027 / 4000000000000 : ℝ) < t → t ≤ (6432545181 / 250000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-55847937122703681319909071 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6432545181 / 250000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_55
  have hV : (669536460042516256253681081436951 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (92531540027 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_54 (Vfield_monotoneOn (show (92531540027 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (92531540027 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_55 : (688983201652322580407136904277429 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (6432545181 / 250000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6432545181 / 250000000000 : ℝ) := by norm_num
  have hs1 : (2005078736141 / 12500000000000 : ℝ) ≤ Real.sqrt (6432545181 / 250000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6432545181 / 250000000000 : ℝ) ≤ (16040629889129 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16040629889129 / 100000000000000 : ℝ) = (100000000000000 / 16040629889129 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2005078736141 / 12500000000000 : ℝ) = (937500000000 / 2005078736141 : ℝ) := by norm_num
  have hL1 : (158779565077 / 6250000000000 : ℝ) ≤ Real.log (1 + (6432545181 / 250000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6432545181 / 250000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-346237576990241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16040629889129 / 100000000000000 : ℝ) ≤ (159051394322079 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (141174493247281761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 16040629889129 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 16040629889129 : ℝ) = (16040629889129 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (937500000000 / 2005078736141 : ℝ) ≤ (109340672406227 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (141174493247281761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16040629889129 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2005078736141 / 12500000000000 : ℝ)) ≤ (109340672406227 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_55 : ∀ t : ℝ, (6432545181 / 250000000000 : ℝ) < t → t ≤ (213931144553 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-69315511681504021599921627 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (213931144553 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_56
  have hV : (688983201652322580407136904277429 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6432545181 / 250000000000 : ℝ) := by norm_num
    refine le_trans V_pt_55 (Vfield_monotoneOn (show (6432545181 / 250000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6432545181 / 250000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_56 : (2786365939203018855156837165079627 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (213931144553 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (213931144553 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (8176397903283 / 50000000000000 : ℝ) ≤ Real.sqrt (213931144553 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (213931144553 / 8000000000000 : ℝ) ≤ (16352795806567 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16352795806567 / 100000000000000 : ℝ) = (100000000000000 / 16352795806567 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8176397903283 / 50000000000000 : ℝ) = (1250000000000 / 2725465967761 : ℝ) := by norm_num
  have hL1 : (1319504556279 / 50000000000000 : ℝ) ≤ Real.log (1 + (213931144553 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((213931144553 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-34306346441541 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16352795806567 / 100000000000000 : ℝ) ≤ (162093253129947 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (140870307366494961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 16352795806567 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 16352795806567 : ℝ) = (16352795806567 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 2725465967761 : ℝ) ≤ (430013340960649 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (140870307366494961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16352795806567 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8176397903283 / 50000000000000 : ℝ)) ≤ (430013340960649 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_56 : ∀ t : ℝ, (213931144553 / 8000000000000 : ℝ) < t → t ≤ (435951987867 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-55352882394415541523786307 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (435951987867 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_57
  have hV : (2786365939203018855156837165079627 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (213931144553 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_56 (Vfield_monotoneOn (show (213931144553 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (213931144553 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_57 : (560319965567471016761220033710599 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (435951987867 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (435951987867 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (1650666509071 / 10000000000000 : ℝ) ≤ Real.sqrt (435951987867 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (435951987867 / 16000000000000 : ℝ) ≤ (16506665090711 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16506665090711 / 100000000000000 : ℝ) = (100000000000000 / 16506665090711 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1650666509071 / 10000000000000 : ℝ) = (750000000000 / 1650666509071 : ℝ) := by norm_num
  have hL1 : (168015047627 / 6250000000000 : ℝ) ≤ Real.log (1 + (435951987867 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((435951987867 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-170756703458497 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16506665090711 / 100000000000000 : ℝ) ≤ (32718300510961 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (140720482424009161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 16506665090711 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 16506665090711 : ℝ) = (16506665090711 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (750000000000 / 1650666509071 : ℝ) ≤ (106618843258373 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (140720482424009161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16506665090711 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1650666509071 / 10000000000000 : ℝ)) ≤ (106618843258373 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_57 : ∀ t : ℝ, (435951987867 / 16000000000000 : ℝ) < t → t ≤ (111010421657 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-276333516009049125281993939 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (111010421657 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_58
  have hV : (560319965567471016761220033710599 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (435951987867 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_57 (Vfield_monotoneOn (show (435951987867 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (435951987867 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_58 : (5633682960665676827964351169215927 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (111010421657 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (111010421657 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (16659113245983 / 100000000000000 : ℝ) ≤ Real.sqrt (111010421657 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (111010421657 / 4000000000000 : ℝ) ≤ (520597288937 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (520597288937 / 3125000000000 : ℝ) = (3125000000000 / 520597288937 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16659113245983 / 100000000000000 : ℝ) = (2500000000000 / 5553037748661 : ℝ) := by norm_num
  have hL1 : (68436204647 / 2500000000000 : ℝ) ≤ Real.log (1 + (111010421657 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((111010421657 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-67997401983249 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (520597288937 / 3125000000000 : ℝ) ≤ (82537591886387 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (140572114302212261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 520597288937 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 520597288937 : ℝ) = (520597288937 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 5553037748661 : ℝ) ≤ (8460471774193 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (140572114302212261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (520597288937 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16659113245983 / 100000000000000 : ℝ)) ≤ (8460471774193 / 20000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_58 : ∀ t : ℝ, (111010421657 / 4000000000000 : ℝ) < t → t ≤ (452131385389 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-137973289911632804893897481 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (452131385389 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_59
  have hV : (5633682960665676827964351169215927 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (111010421657 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_58 (Vfield_monotoneOn (show (111010421657 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (111010421657 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_59 : (5664176626829281374758357598696639 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (452131385389 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (452131385389 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (16810178936231 / 100000000000000 : ℝ) ≤ Real.sqrt (452131385389 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (452131385389 / 16000000000000 : ℝ) ≤ (2101272367029 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2101272367029 / 12500000000000 : ℝ) = (12500000000000 / 2101272367029 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16810178936231 / 100000000000000 : ℝ) = (7500000000000 / 16810178936231 : ℝ) := by norm_num
  have hL1 : (278663140793 / 10000000000000 : ℝ) ≤ Real.log (1 + (452131385389 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((452131385389 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-169241780969597 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2101272367029 / 12500000000000 : ℝ) ≤ (2602260737817 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (140425163957460861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 2101272367029 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 2101272367029 : ℝ) = (2101272367029 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 16810178936231 : ℝ) ≤ (41965453408611 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (140425163957460861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2101272367029 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16810178936231 / 100000000000000 : ℝ)) ≤ (41965453408611 / 100000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_59 : ∀ t : ℝ, (452131385389 / 16000000000000 : ℝ) < t → t ≤ (912352469539 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-275765685175219109942953999 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (912352469539 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_60
  have hV : (5664176626829281374758357598696639 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (452131385389 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_59 (Vfield_monotoneOn (show (452131385389 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (452131385389 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_60 : (2839712916321794302008272873245121 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (912352469539 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (912352469539 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (8442602482809 / 50000000000000 : ℝ) ≤ Real.sqrt (912352469539 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (912352469539 / 32000000000000 : ℝ) ≤ (16885204965619 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (16885204965619 / 100000000000000 : ℝ) = (100000000000000 / 16885204965619 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8442602482809 / 50000000000000 : ℝ) = (1250000000000 / 2814200827603 : ℝ) := by norm_num
  have hL1 : (2811213950719 / 100000000000000 : ℝ) ≤ Real.log (1 + (912352469539 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((912352469539 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-337740230195459 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (16885204965619 / 100000000000000 : ℝ) ≤ (167274239526411 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (140352208726848561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 16885204965619 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 16885204965619 : ℝ) = (16885204965619 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 2814200827603 : ℝ) ≤ (16720000150339 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (140352208726848561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (16885204965619 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8442602482809 / 50000000000000 : ℝ)) ≤ (16720000150339 / 40000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_60 : ∀ t : ℝ, (912352469539 / 32000000000000 : ℝ) < t → t ≤ (9204421683 / 320000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-137795895449762999993813881 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9204421683 / 320000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_61
  have hV : (2839712916321794302008272873245121 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (912352469539 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_60 (Vfield_monotoneOn (show (912352469539 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (912352469539 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_61 : (5694675857122282302896142044394241 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9204421683 / 320000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9204421683 / 320000000000 : ℝ) := by norm_num
  have hs1 : (16959899103289 / 100000000000000 : ℝ) ≤ Real.sqrt (9204421683 / 320000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9204421683 / 320000000000 : ℝ) ≤ (1695989910329 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1695989910329 / 10000000000000 : ℝ) = (10000000000000 / 1695989910329 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (16959899103289 / 100000000000000 : ℝ) = (7500000000000 / 16959899103289 : ℝ) := by norm_num
  have hL1 : (1417895225989 / 50000000000000 : ℝ) ≤ Real.log (1 + (9204421683 / 320000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9204421683 / 320000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-168501191564131 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1695989910329 / 10000000000000 : ℝ) ≤ (168000386015171 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (140279594077972561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 1695989910329 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 1695989910329 : ℝ) = (1695989910329 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 16959899103289 : ℝ) ≤ (416364946584037 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (140279594077972561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1695989910329 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (16959899103289 / 100000000000000 : ℝ)) ≤ (416364946584037 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_61 : ∀ t : ℝ, (9204421683 / 320000000000 : ℝ) < t → t ≤ (928531867061 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-27542412153704319667164653 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (928531867061 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_62
  have hV : (5694675857122282302896142044394241 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9204421683 / 320000000000 : ℝ) := by norm_num
    refine le_trans V_pt_61 (Vfield_monotoneOn (show (9204421683 / 320000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9204421683 / 320000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_62 : (1141985230733192635046428531555067 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (928531867061 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (928531867061 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (3406853143043 / 20000000000000 : ℝ) ≤ Real.sqrt (928531867061 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (928531867061 / 32000000000000 : ℝ) ≤ (1064641607201 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1064641607201 / 6250000000000 : ℝ) = (6250000000000 / 1064641607201 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3406853143043 / 20000000000000 : ℝ) = (1500000000000 / 3406853143043 : ℝ) := by norm_num
  have hL1 : (1430180457339 / 50000000000000 : ℝ) ≤ Real.log (1 + (928531867061 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((928531867061 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-42033742549081 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1064641607201 / 6250000000000 : ℝ) ≤ (21090396349253 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (140207315600087261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 1064641607201 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 1064641607201 : ℝ) = (1064641607201 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1500000000000 / 3406853143043 : ℝ) ≤ (103687245606923 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (140207315600087261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1064641607201 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3406853143043 / 20000000000000 : ℝ)) ≤ (103687245606923 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_62 : ∀ t : ℝ, (928531867061 / 32000000000000 : ℝ) < t → t ≤ (468310782911 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-17203877755631245144121899 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (468310782911 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_63
  have hV : (1141985230733192635046428531555067 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (928531867061 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_62 (Vfield_monotoneOn (show (928531867061 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (928531867061 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_63 : (1431294048831629018731909023598511 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (468310782911 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (468310782911 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (4277077268119 / 25000000000000 : ℝ) ≤ Real.sqrt (468310782911 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (468310782911 / 16000000000000 : ℝ) ≤ (17108309072477 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17108309072477 / 100000000000000 : ℝ) = (100000000000000 / 17108309072477 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4277077268119 / 25000000000000 : ℝ) = (1875000000000 / 4277077268119 : ℝ) := by norm_num
  have hL1 : (360615667723 / 12500000000000 : ℝ) ≤ Real.log (1 + (468310782911 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((468310782911 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-33554282339629 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17108309072477 / 100000000000000 : ℝ) ≤ (84721318507943 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (140135368977901061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 17108309072477 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 17108309072477 : ℝ) = (17108309072477 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 4277077268119 : ℝ) ≤ (413151741493551 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (140135368977901061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17108309072477 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4277077268119 / 25000000000000 : ℝ)) ≤ (413151741493551 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_63 : ∀ t : ℝ, (468310782911 / 16000000000000 : ℝ) < t → t ≤ (944711264583 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-275105033223790970078886881 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (944711264583 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_64
  have hV : (1431294048831629018731909023598511 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (468310782911 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_63 (Vfield_monotoneOn (show (468310782911 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (468310782911 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_64 : (2870212737023269993415328061744909 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (944711264583 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (944711264583 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (8591016677061 / 50000000000000 : ℝ) ≤ Real.sqrt (944711264583 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (944711264583 / 32000000000000 : ℝ) ≤ (17182033354123 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17182033354123 / 100000000000000 : ℝ) = (100000000000000 / 17182033354123 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8591016677061 / 50000000000000 : ℝ) = (1250000000000 / 2863672225687 : ℝ) := by norm_num
  have hL1 : (2909483736261 / 100000000000000 : ℝ) ≤ Real.log (1 + (944711264583 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((944711264583 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-334820955248881 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17182033354123 / 100000000000000 : ℝ) ≤ (85079413453929 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (140063749988703861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 17182033354123 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 17182033354123 : ℝ) = (17182033354123 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 2863672225687 : ℝ) ≤ (411572863965117 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (140063749988703861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17182033354123 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8591016677061 / 50000000000000 : ℝ)) ≤ (411572863965117 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_64 : ∀ t : ℝ, (944711264583 / 32000000000000 : ℝ) < t → t ≤ (59550060209 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-274952646739044420081965309 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (59550060209 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_65
  have hV : (2870212737023269993415328061744909 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (944711264583 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_64 (Vfield_monotoneOn (show (944711264583 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (944711264583 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_65 : (5755673499934530010232567702260401 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (59550060209 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (59550060209 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (17255442649929 / 100000000000000 : ℝ) ≤ Real.sqrt (59550060209 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (59550060209 / 2000000000000 : ℝ) ≤ (1725544264993 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1725544264993 / 10000000000000 : ℝ) = (10000000000000 / 1725544264993 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17255442649929 / 100000000000000 : ℝ) = (2500000000000 / 5751814216643 : ℝ) := by norm_num
  have hL1 : (183377256317 / 6250000000000 : ℝ) ≤ Real.log (1 + (59550060209 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((59550060209 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-334104260713343 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1725544264993 / 10000000000000 : ℝ) ≤ (21358972724863 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (139992454499599261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 1725544264993 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 1725544264993 : ℝ) = (1725544264993 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 5751814216643 : ℝ) ≤ (41001199966059 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (139992454499599261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1725544264993 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17255442649929 / 100000000000000 : ℝ)) ≤ (41001199966059 / 100000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_65 : ∀ t : ℝ, (59550060209 / 2000000000000 : ℝ) < t → t ≤ (192178132421 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-274804507833090220391731727 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (192178132421 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_66
  have hV : (5755673499934530010232567702260401 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (59550060209 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_65 (Vfield_monotoneOn (show (59550060209 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (59550060209 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_66 : (5770919800568470570456499165163529 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (192178132421 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (192178132421 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (17328540963041 / 100000000000000 : ℝ) ≤ Real.sqrt (192178132421 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (192178132421 / 6400000000000 : ℝ) ≤ (8664270481521 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8664270481521 / 50000000000000 : ℝ) = (50000000000000 / 8664270481521 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17328540963041 / 100000000000000 : ℝ) = (7500000000000 / 17328540963041 : ℝ) := by norm_num
  have hL1 : (369822804897 / 12500000000000 : ℝ) ≤ Real.log (1 + (192178132421 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((192178132421 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-20837041634923 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8664270481521 / 50000000000000 : ℝ) ≤ (85790771073193 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (139921478464851061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 8664270481521 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 8664270481521 : ℝ) = (8664270481521 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 17328540963041 : ℝ) ≤ (408468807702847 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (139921478464851061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8664270481521 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17328540963041 / 100000000000000 : ℝ)) ≤ (408468807702847 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_66 : ∀ t : ℝ, (192178132421 / 6400000000000 : ℝ) < t → t ≤ (484490180433 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-274660291979927843618913863 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (484490180433 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_67
  have hV : (5770919800568470570456499165163529 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (192178132421 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_66 (Vfield_monotoneOn (show (192178132421 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (192178132421 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_67 : (5786163920334883723850123556385187 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (484490180433 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (484490180433 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (17401332212523 / 100000000000000 : ℝ) ≤ Real.sqrt (484490180433 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (484490180433 / 16000000000000 : ℝ) ≤ (4350333053131 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4350333053131 / 25000000000000 : ℝ) = (25000000000000 / 4350333053131 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17401332212523 / 100000000000000 : ℝ) = (2500000000000 / 5800444070841 : ℝ) := by norm_num
  have hL1 : (2983122753531 / 100000000000000 : ℝ) ≤ Real.log (1 + (484490180433 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((484490180433 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-332686099515021 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4350333053131 / 25000000000000 : ℝ) ≤ (86144073780851 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (139850817923319461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 4350333053131 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 4350333053131 : ℝ) = (4350333053131 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 5800444070841 : ℝ) ≤ (203471478101471 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (139850817923319461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4350333053131 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17401332212523 / 100000000000000 : ℝ)) ≤ (203471478101471 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_67 : ∀ t : ℝ, (484490180433 / 16000000000000 : ℝ) < t → t ≤ (977070059627 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-54903943407445428102957827 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (977070059627 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_68
  have hV : (5786163920334883723850123556385187 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (484490180433 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_67 (Vfield_monotoneOn (show (484490180433 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (484490180433 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_68 : (580140541979330458313915164018789 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (977070059627 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (977070059627 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (1747382023581 / 10000000000000 : ℝ) ≤ Real.sqrt (977070059627 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (977070059627 / 32000000000000 : ℝ) ≤ (17473820235811 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17473820235811 / 100000000000000 : ℝ) = (100000000000000 / 17473820235811 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1747382023581 / 10000000000000 : ℝ) = (250000000000 / 582460674527 : ℝ) := by norm_num
  have hL1 : (1503828523547 / 50000000000000 : ℝ) ≤ Real.log (1 + (977070059627 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((977070059627 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-165992245114469 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17473820235811 / 100000000000000 : ℝ) ≤ (540598865109 / 3125000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (139780468996001661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 17473820235811 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 17473820235811 : ℝ) = (17473820235811 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (250000000000 / 582460674527 : ℝ) ≤ (405434121956879 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (139780468996001661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17473820235811 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1747382023581 / 10000000000000 : ℝ)) ≤ (405434121956879 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_68 : ∀ t : ℝ, (977070059627 / 32000000000000 : ℝ) < t → t ≤ (246289939597 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-274382535657572164657660173 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (246289939597 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_69
  have hV : (580140541979330458313915164018789 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (977070059627 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_68 (Vfield_monotoneOn (show (977070059627 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (977070059627 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_69 : (1454160968767377811041766920477823 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (246289939597 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (246289939597 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (4386502197767 / 25000000000000 : ℝ) ≤ Real.sqrt (246289939597 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (246289939597 / 8000000000000 : ℝ) ≤ (17546008791069 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17546008791069 / 100000000000000 : ℝ) = (100000000000000 / 17546008791069 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4386502197767 / 25000000000000 : ℝ) = (1875000000000 / 4386502197767 : ℝ) := by norm_num
  have hL1 : (1516092661409 / 50000000000000 : ℝ) ≤ Real.log (1 + (246289939597 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((246289939597 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6625755384441 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17546008791069 / 100000000000000 : ℝ) ≤ (173692047958299 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (139710427883659761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 17546008791069 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 17546008791069 : ℝ) = (17546008791069 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 4386502197767 : ℝ) ≤ (100985497538691 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (139710427883659761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17546008791069 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4386502197767 / 25000000000000 : ℝ)) ≤ (100985497538691 / 250000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_69 : ∀ t : ℝ, (246289939597 / 8000000000000 : ℝ) < t → t ≤ (100133915591 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-34264687994531223147630409 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (100133915591 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_70
  have hV : (1454160968767377811041766920477823 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (246289939597 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_69 (Vfield_monotoneOn (show (246289939597 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (246289939597 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_70 : (5847110031950114078359204154163299 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (100133915591 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (100133915591 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (17689502147371 / 100000000000000 : ℝ) ≤ Real.sqrt (100133915591 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (100133915591 / 3200000000000 : ℝ) ≤ (4422375536843 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4422375536843 / 25000000000000 : ℝ) = (25000000000000 / 4422375536843 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17689502147371 / 100000000000000 : ℝ) = (7500000000000 / 17689502147371 : ℝ) := by norm_num
  have hL1 : (61624476651 / 2000000000000 : ℝ) ≤ Real.log (1 + (100133915591 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((100133915591 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-32990872286197 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4422375536843 / 25000000000000 : ℝ) ≤ (43770945968313 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (139571254292164461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 4422375536843 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 4422375536843 : ℝ) = (4422375536843 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 17689502147371 : ℝ) ≤ (200503307475357 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (139571254292164461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4422375536843 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17689502147371 / 100000000000000 : ℝ)) ≤ (200503307475357 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_70 : ∀ t : ℝ, (100133915591 / 3200000000000 : ℝ) < t → t ≤ (127189819179 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-34232964769285211383345873 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (127189819179 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_71
  have hV : (5847110031950114078359204154163299 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (100133915591 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_70 (Vfield_monotoneOn (show (100133915591 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (100133915591 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_71 : (5877559289862511668694296343502139 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (127189819179 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (127189819179 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (17831840845731 / 100000000000000 : ℝ) ≤ Real.sqrt (127189819179 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (127189819179 / 4000000000000 : ℝ) ≤ (4457960211433 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4457960211433 / 25000000000000 : ℝ) = (25000000000000 / 4457960211433 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17831840845731 / 100000000000000 : ℝ) = (2500000000000 / 5943946948577 : ℝ) := by norm_num
  have hL1 : (626047661263 / 20000000000000 : ℝ) ≤ Real.log (1 + (127189819179 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((127189819179 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-328548435784569 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4457960211433 / 25000000000000 : ℝ) ≤ (7058545765591 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (139433268265512161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 4457960211433 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 4457960211433 : ℝ) = (4457960211433 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (2500000000000 / 5943946948577 : ℝ) ≤ (398134469669709 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (139433268265512161923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4457960211433 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17831840845731 / 100000000000000 : ℝ)) ≤ (398134469669709 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_71 : ∀ t : ℝ, (127189819179 / 4000000000000 : ℝ) < t → t ≤ (516848975477 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-54723996732700034674662857 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (516848975477 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_72
  have hV : (5877559289862511668694296343502139 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (127189819179 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_71 (Vfield_monotoneOn (show (127189819179 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (127189819179 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_72 : (5907988762082384439105445192514387 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (516848975477 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (516848975477 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (17973052319323 / 100000000000000 : ℝ) ≤ Real.sqrt (516848975477 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (516848975477 / 16000000000000 : ℝ) ≤ (4493263079831 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4493263079831 / 25000000000000 : ℝ) = (25000000000000 / 4493263079831 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17973052319323 / 100000000000000 : ℝ) = (7500000000000 / 17973052319323 : ℝ) := by norm_num
  have hL1 : (3179228767663 / 100000000000000 : ℝ) ≤ Real.log (1 + (516848975477 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((516848975477 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-327206404463523 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4493263079831 / 25000000000000 : ℝ) ≤ (88915953103291 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (139296442058831461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 4493263079831 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 4493263079831 : ℝ) = (4493263079831 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 17973052319323 : ℝ) ≤ (197661655484021 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (139296442058831461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4493263079831 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17973052319323 / 100000000000000 : ℝ)) ≤ (197661655484021 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_72 : ∀ t : ℝ, (516848975477 / 16000000000000 : ℝ) < t → t ≤ (262469337119 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2187082532882806593353491 / 800000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (262469337119 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_73
  have hV : (5907988762082384439105445192514387 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (516848975477 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_72 (Vfield_monotoneOn (show (516848975477 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (516848975477 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_73 : (1484598940242204398496198139718927 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (262469337119 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (262469337119 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (4528290732983 / 25000000000000 : ℝ) ≤ Real.sqrt (262469337119 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (262469337119 / 8000000000000 : ℝ) ≤ (18113162931933 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18113162931933 / 100000000000000 : ℝ) = (100000000000000 / 18113162931933 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4528290732983 / 25000000000000 : ℝ) = (1875000000000 / 4528290732983 : ℝ) := by norm_num
  have hL1 : (3228195240109 / 100000000000000 : ℝ) ≤ Real.log (1 + (262469337119 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((262469337119 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-325882145377389 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18113162931933 / 100000000000000 : ℝ) ≤ (44797209189517 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (139160749003682861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 18113162931933 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 18113162931933 : ℝ) = (18113162931933 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 4528290732983 : ℝ) ≤ (392571005638041 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (139160749003682861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18113162931933 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4528290732983 / 25000000000000 : ℝ)) ≤ (392571005638041 / 1000000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_73 : ∀ t : ℝ, (262469337119 / 8000000000000 : ℝ) < t → t ≤ (6763975897 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-68235003809366230643256057 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (6763975897 / 200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_74
  have hV : (1484598940242204398496198139718927 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (262469337119 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_73 (Vfield_monotoneOn (show (262469337119 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (262469337119 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_74 : (5999132500354233209975727495960393 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (6763975897 / 200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (6763975897 / 200000000000 : ℝ) := by norm_num
  have hs1 : (18390182023297 / 100000000000000 : ℝ) ≤ Real.sqrt (6763975897 / 200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (6763975897 / 200000000000 : ℝ) ≤ (9195091011649 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9195091011649 / 50000000000000 : ℝ) = (50000000000000 / 9195091011649 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (18390182023297 / 100000000000000 : ℝ) = (7500000000000 / 18390182023297 : ℝ) := by norm_num
  have hL1 : (332605631219 / 10000000000000 : ℝ) ≤ Real.log (1 + (6763975897 / 200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((6763975897 / 200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-64657020728137 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9195091011649 / 50000000000000 : ℝ) ≤ (181869719656047 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (138892660713884961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 9195091011649 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 9195091011649 : ℝ) = (9195091011649 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 18390182023297 : ℝ) ≤ (193617466113309 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (138892660713884961923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9195091011649 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (18390182023297 / 100000000000000 : ℝ)) ≤ (193617466113309 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_74 : ∀ t : ℝ, (6763975897 / 200000000000 : ℝ) < t → t ≤ (278648734641 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-272522572618026273014758019 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (278648734641 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_75
  have hV : (5999132500354233209975727495960393 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (6763975897 / 200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_74 (Vfield_monotoneOn (show (6763975897 / 200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (6763975897 / 200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_75 : (1514937870398872639216977559618221 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (278648734641 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (278648734641 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (4665772432709 / 25000000000000 : ℝ) ≤ Real.sqrt (278648734641 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (278648734641 / 8000000000000 : ℝ) ≤ (18663089730837 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18663089730837 / 100000000000000 : ℝ) = (100000000000000 / 18663089730837 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4665772432709 / 25000000000000 : ℝ) = (1875000000000 / 4665772432709 : ℝ) := by norm_num
  have hL1 : (3423821709997 / 100000000000000 : ℝ) ≤ Real.log (1 + (278648734641 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((278648734641 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-320753804403077 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18663089730837 / 100000000000000 : ℝ) ≤ (184508232006191 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (138628809478870561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 18663089730837 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 18663089730837 : ℝ) = (18663089730837 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 4665772432709 : ℝ) ≤ (47763892242603 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (138628809478870561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18663089730837 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4665772432709 / 25000000000000 : ℝ)) ≤ (47763892242603 / 125000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_75 : ∀ t : ℝ, (278648734641 / 8000000000000 : ℝ) < t → t ≤ (143369216701 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-272129057255004506327381047 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (143369216701 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_76
  have hV : (1514937870398872639216977559618221 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (278648734641 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_75 (Vfield_monotoneOn (show (278648734641 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (278648734641 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_76 : (3060118536172900152759964791020367 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (143369216701 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (143369216701 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (9466031926743 / 50000000000000 : ℝ) ≤ Real.sqrt (143369216701 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (143369216701 / 4000000000000 : ℝ) ≤ (18932063853487 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18932063853487 / 100000000000000 : ℝ) = (100000000000000 / 18932063853487 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9466031926743 / 50000000000000 : ℝ) = (1250000000000 / 3155343975581 : ℝ) := by norm_num
  have hL1 : (3521491620419 / 100000000000000 : ℝ) ≤ Real.log (1 + (143369216701 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((143369216701 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-318285001216241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18932063853487 / 100000000000000 : ℝ) ≤ (187106173891251 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (138369015290364561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 18932063853487 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 18932063853487 : ℝ) = (18932063853487 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 3155343975581 : ℝ) ≤ (188592941845467 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (138369015290364561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18932063853487 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9466031926743 / 50000000000000 : ℝ)) ≤ (188592941845467 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_76 : ∀ t : ℝ, (143369216701 / 4000000000000 : ℝ) < t → t ≤ (75729457731 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-67850553301311515181694499 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (75729457731 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_77
  have hV : (3060118536172900152759964791020367 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (143369216701 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_76 (Vfield_monotoneOn (show (143369216701 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (143369216701 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_77 : (3120377846228692737548945477160047 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (75729457731 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (75729457731 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (9729430721463 / 50000000000000 : ℝ) ≤ Real.sqrt (75729457731 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (75729457731 / 2000000000000 : ℝ) ≤ (19458861442927 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19458861442927 / 100000000000000 : ℝ) = (100000000000000 / 19458861442927 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9729430721463 / 50000000000000 : ℝ) = (1250000000000 / 3243143573821 : ℝ) := by norm_num
  have hL1 : (3716545723939 / 100000000000000 : ℝ) ≤ Real.log (1 + (75729457731 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((75729457731 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1254092194201 / 400000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19458861442927 / 100000000000000 : ℝ) ≤ (192186931182941 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (137860939561195561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 19458861442927 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 19458861442927 : ℝ) = (19458861442927 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1250000000000 / 3243143573821 : ℝ) ≤ (183940991600099 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (137860939561195561923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19458861442927 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9729430721463 / 50000000000000 : ℝ)) ≤ (183940991600099 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_77 : ∀ t : ℝ, (75729457731 / 2000000000000 : ℝ) < t → t ≤ (20954789123 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-16883417697812042294047289 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20954789123 / 500000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_78
  have hV : (3120377846228692737548945477160047 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (75729457731 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_77 (Vfield_monotoneOn (show (75729457731 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (75729457731 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_78 : (1619926395554128206850897301772897 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (20954789123 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20954789123 / 500000000000 : ℝ) := by norm_num
  have hs1 : (5117957249113 / 25000000000000 : ℝ) ≤ Real.sqrt (20954789123 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20954789123 / 500000000000 : ℝ) ≤ (20471828996453 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (20471828996453 / 100000000000000 : ℝ) = (100000000000000 / 20471828996453 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5117957249113 / 25000000000000 : ℝ) = (1875000000000 / 5117957249113 : ℝ) := by norm_num
  have hL1 : (2052758122533 / 50000000000000 : ℝ) ≤ Real.log (1 + (20954789123 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20954789123 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-38078723355059 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (20471828996453 / 100000000000000 : ℝ) ≤ (201928233271379 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (136886809352351761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 20471828996453 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 20471828996453 : ℝ) = (20471828996453 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (1875000000000 / 5117957249113 : ℝ) ≤ (175585945679559 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (136886809352351761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (20471828996453 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5117957249113 / 25000000000000 : ℝ)) ≤ (175585945679559 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_78 : ∀ t : ℝ, (20954789123 / 500000000000 : ℝ) < t → t ≤ (694494763253 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-133752621245920384190080933 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (694494763253 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_79
  have hV : (1619926395554128206850897301772897 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20954789123 / 500000000000 : ℝ) := by norm_num
    refine le_trans V_pt_78 (Vfield_monotoneOn (show (20954789123 / 500000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20954789123 / 500000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_79 : (6567323836145583869159951439940741 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (694494763253 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (694494763253 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (20834088101789 / 100000000000000 : ℝ) ≤ Real.sqrt (694494763253 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (694494763253 / 16000000000000 : ℝ) ≤ (2083408810179 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2083408810179 / 10000000000000 : ℝ) = (10000000000000 / 2083408810179 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (20834088101789 / 100000000000000 : ℝ) = (7500000000000 / 20834088101789 : ℝ) := by norm_num
  have hL1 : (4249028793977 / 100000000000000 : ℝ) ≤ Real.log (1 + (694494763253 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((694494763253 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-301530410303843 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2083408810179 / 10000000000000 : ℝ) ≤ (205402622899849 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (136539370389504761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 2083408810179 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 2083408810179 : ℝ) = (2083408810179 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 20834088101789 : ℝ) ≤ (5399125545609 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (136539370389504761923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2083408810179 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (20834088101789 / 100000000000000 : ℝ)) ≤ (5399125545609 / 15625000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_79 : ∀ t : ℝ, (694494763253 / 16000000000000 : ℝ) < t → t ≤ (1412931037823 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-266815056315630100554462937 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1412931037823 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_80
  have hV : (6567323836145583869159951439940741 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (694494763253 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_79 (Vfield_monotoneOn (show (694494763253 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (694494763253 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
