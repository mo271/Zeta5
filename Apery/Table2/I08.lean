import Apery.Table2.U08
import Apery.Table2.U09

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_320 : (8446991359555868591761059914672053 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (37663773450957 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (37663773450957 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (27122326139437 / 50000000000000 : ℝ) ≤ Real.sqrt (37663773450957 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (37663773450957 / 128000000000000 : ℝ) ≤ (433957218231 / 800000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (433957218231 / 800000000000 : ℝ) = (800000000000 / 433957218231 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27122326139437 / 50000000000000 : ℝ) = (3750000000000 / 27122326139437 : ℝ) := by norm_num
  have hL1 : (25793000927767 / 100000000000000 : ℝ) ≤ Real.log (1 + (37663773450957 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((37663773450957 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-12043954594937 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (18081550759625 / 71255010366186 : ℝ) ≤ (248512752818681 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (433957218231 / 800000000000 : ℝ) ≤ (248512752818681 / 500000000000000 : ℝ) := by
    have hw : (56882515549279 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (433957218231 / 800000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (433957218231 / 800000000000 : ℝ) / (1 + (56882515549279 / 50000000000000 : ℝ)) = (18081550759625 / 71255010366186 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107377082115753461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (800000000000 / 433957218231 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (800000000000 / 433957218231 : ℝ) = (433957218231 / 800000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 27122326139437 : ℝ) ≤ (137391414482113 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107377082115753461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (433957218231 / 800000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27122326139437 / 50000000000000 : ℝ)) ≤ (137391414482113 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_320 : ∀ t : ℝ, (37663773450957 / 128000000000000 : ℝ) < t → t ≤ (3774151700821 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-81693865023819144576255407 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3774151700821 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_321
  have hV : (8446991359555868591761059914672053 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (37663773450957 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_320 (Vfield_monotoneOn (show (37663773450957 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (37663773450957 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_321 : (8456479242998576131736842850621017 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (3774151700821 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3774151700821 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (27150303940593 / 50000000000000 : ℝ) ≤ Real.sqrt (3774151700821 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3774151700821 / 12800000000000 : ℝ) ≤ (54300607881187 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (54300607881187 / 100000000000000 : ℝ) = (100000000000000 / 54300607881187 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27150303940593 / 50000000000000 : ℝ) = (1250000000000 / 9050101313531 : ℝ) := by norm_num
  have hL1 : (25839918439899 / 100000000000000 : ℝ) ≤ Real.log (1 + (3774151700821 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3774151700821 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7514825501411 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54300607881187 / 213791722090257 : ℝ) ≤ (124364436203831 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (54300607881187 / 100000000000000 : ℝ) ≤ (124364436203831 / 250000000000000 : ℝ) := by
    have hw : (113791722090257 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (54300607881187 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (54300607881187 / 100000000000000 : ℝ) / (1 + (113791722090257 / 100000000000000 : ℝ)) = (54300607881187 / 213791722090257 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107333858197957261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 54300607881187 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 54300607881187 : ℝ) = (54300607881187 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 9050101313531 : ℝ) ≤ (137251607850987 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107333858197957261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (54300607881187 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27150303940593 / 50000000000000 : ℝ)) ≤ (137251607850987 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_321 : ∀ t : ℝ, (3774151700821 / 12800000000000 : ℝ) < t → t ≤ (37819260565463 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-163202829369876740284492817 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (37819260565463 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_322
  have hV : (8456479242998576131736842850621017 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3774151700821 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_321 (Vfield_monotoneOn (show (3774151700821 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3774151700821 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_322 : (16931916986363385194076342590089203 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (37819260565463 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (37819260565463 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (54356505881787 / 100000000000000 : ℝ) ≤ Real.sqrt (37819260565463 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (37819260565463 / 128000000000000 : ℝ) ≤ (13589126470447 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13589126470447 / 25000000000000 : ℝ) = (25000000000000 / 13589126470447 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (54356505881787 / 100000000000000 : ℝ) = (2500000000000 / 18118835293929 : ℝ) := by norm_num
  have hL1 : (202240733983 / 781250000000 : ℝ) ≤ Real.log (1 + (37819260565463 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((37819260565463 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15004409834447 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (13589126470447 / 53454601705696 : ℝ) ≤ (248944668273147 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13589126470447 / 25000000000000 : ℝ) ≤ (248944668273147 / 500000000000000 : ℝ) := by
    have hw : (889206303303 / 781250000000 : ℝ) ≤ Real.sqrt (1 + (13589126470447 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (13589126470447 / 25000000000000 : ℝ) / (1 + (889206303303 / 781250000000 : ℝ)) = (13589126470447 / 53454601705696 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107290699024860261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 13589126470447 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 13589126470447 : ℝ) = (13589126470447 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 18118835293929 : ℝ) ≤ (137112227159537 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107290699024860261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13589126470447 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (54356505881787 / 100000000000000 : ℝ)) ≤ (137112227159537 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_322 : ∀ t : ℝ, (37819260565463 / 128000000000000 : ℝ) < t → t ≤ (9474251030679 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-163019068496811354805450809 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9474251030679 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_323
  have hV : (16931916986363385194076342590089203 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (37819260565463 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_322 (Vfield_monotoneOn (show (37819260565463 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (37819260565463 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_323 : (16950858265128396504528282416170031 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9474251030679 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9474251030679 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (54412346458199 / 100000000000000 : ℝ) ≤ Real.sqrt (9474251030679 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9474251030679 / 32000000000000 : ℝ) ≤ (272061732291 / 500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (272061732291 / 500000000000 : ℝ) = (500000000000 / 272061732291 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (54412346458199 / 100000000000000 : ℝ) = (7500000000000 / 54412346458199 : ℝ) := by norm_num
  have hL1 : (25933687478169 / 100000000000000 : ℝ) ≤ Real.log (1 + (9474251030679 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9474251030679 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-14979219532701 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54412346458200 / 213845085300539 : ℝ) ≤ (1993281131229 / 8000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (272061732291 / 500000000000 : ℝ) ≤ (1993281131229 / 4000000000000 : ℝ) := by
    have hw : (113845085300539 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (272061732291 / 500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (272061732291 / 500000000000 : ℝ) / (1 + (113845085300539 / 100000000000000 : ℝ)) = (54412346458200 / 213845085300539 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107247604398764661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (500000000000 / 272061732291 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (500000000000 / 272061732291 : ℝ) = (272061732291 / 500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 54412346458199 : ℝ) ≤ (68486635124639 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107247604398764661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (272061732291 / 500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (54412346458199 / 100000000000000 : ℝ)) ≤ (68486635124639 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_323 : ∀ t : ℝ, (9474251030679 / 32000000000000 : ℝ) < t → t ≤ (37974747679969 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-162836419215277365468757623 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (37974747679969 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_324
  have hV : (16950858265128396504528282416170031 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9474251030679 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_323 (Vfield_monotoneOn (show (9474251030679 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9474251030679 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_324 : (16969782367017877754743854418076453 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (37974747679969 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (37974747679969 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (54468129787037 / 100000000000000 : ℝ) ≤ Real.sqrt (37974747679969 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (37974747679969 / 128000000000000 : ℝ) ≤ (27234064893519 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (27234064893519 / 50000000000000 : ℝ) = (50000000000000 / 27234064893519 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (54468129787037 / 100000000000000 : ℝ) = (7500000000000 / 54468129787037 : ℝ) := by norm_num
  have hL1 : (25980539045531 / 100000000000000 : ℝ) ≤ Real.log (1 + (37974747679969 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((37974747679969 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-119632639143847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (9078021631173 / 35645292921320 : ℝ) ≤ (249375292782697 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (27234064893519 / 50000000000000 : ℝ) ≤ (249375292782697 / 500000000000000 : ℝ) := by
    have hw : (1423396969099 / 1250000000000 : ℝ) ≤ Real.sqrt (1 + (27234064893519 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (27234064893519 / 50000000000000 : ℝ) / (1 + (1423396969099 / 1250000000000 : ℝ)) = (9078021631173 / 35645292921320 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107204574122950261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 27234064893519 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 27234064893519 : ℝ) = (27234064893519 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 54468129787037 : ℝ) ≤ (136834734976999 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107204574122950261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (27234064893519 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (54468129787037 / 100000000000000 : ℝ)) ≤ (136834734976999 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_324 : ∀ t : ℝ, (37974747679969 / 128000000000000 : ℝ) < t → t ≤ (19026245618611 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-20331856844759257691534037 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19026245618611 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_325
  have hV : (16969782367017877754743854418076453 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (37974747679969 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_324 (Vfield_monotoneOn (show (37974747679969 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (37974747679969 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_325 : (1698868933656426314330105370369369 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (19026245618611 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19026245618611 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (5452385604401 / 10000000000000 : ℝ) ≤ Real.sqrt (19026245618611 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19026245618611 / 64000000000000 : ℝ) ≤ (54523856044011 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (54523856044011 / 100000000000000 : ℝ) = (100000000000000 / 54523856044011 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5452385604401 / 10000000000000 : ℝ) = (750000000000 / 5452385604401 : ℝ) := by norm_num
  have hL1 : (13013684336239 / 50000000000000 : ℝ) ≤ Real.log (1 + (19026245618611 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19026245618611 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4777277027813 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (18174618681337 / 71299474503106 : ℝ) ≤ (249590123389089 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (54523856044011 / 100000000000000 : ℝ) ≤ (249590123389089 / 500000000000000 : ℝ) := by
    have hw : (56949211754659 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (54523856044011 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (54523856044011 / 100000000000000 : ℝ) / (1 + (56949211754659 / 50000000000000 : ℝ)) = (18174618681337 / 71299474503106 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107161608001671861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 54523856044011 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 54523856044011 : ℝ) = (54523856044011 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 5452385604401 : ℝ) ≤ (136696619214641 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107161608001671861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (54523856044011 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5452385604401 / 10000000000000 : ℝ)) ≤ (136696619214641 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_325 : ∀ t : ℝ, (19026245618611 / 64000000000000 : ℝ) < t → t ≤ (1525209391779 / 5120000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-40618587421981734936285733 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1525209391779 / 5120000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_326
  have hV : (1698868933656426314330105370369369 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19026245618611 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_325 (Vfield_monotoneOn (show (19026245618611 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19026245618611 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_326 : (17007579218109213826963102527057939 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1525209391779 / 5120000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1525209391779 / 5120000000000 : ℝ) := by norm_num
  have hs1 : (54579525403931 / 100000000000000 : ℝ) ≤ Real.sqrt (1525209391779 / 5120000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1525209391779 / 5120000000000 : ℝ) ≤ (13644881350983 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13644881350983 / 25000000000000 : ℝ) = (25000000000000 / 13644881350983 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (54579525403931 / 100000000000000 : ℝ) = (7500000000000 / 54579525403931 : ℝ) := by norm_num
  have hL1 : (521483527591 / 2000000000000 : ℝ) ≤ Real.log (1 + (1525209391779 / 5120000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1525209391779 / 5120000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2384632285977 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (18193175134644 / 71308361083039 : ℝ) ≤ (249804634196703 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13644881350983 / 25000000000000 : ℝ) ≤ (249804634196703 / 500000000000000 : ℝ) := by
    have hw : (113925083249117 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (13644881350983 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (13644881350983 / 25000000000000 : ℝ) / (1 + (113925083249117 / 100000000000000 : ℝ)) = (18193175134644 / 71308361083039 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107118705840149061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 13644881350983 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 13644881350983 : ℝ) = (13644881350983 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 54579525403931 : ℝ) ≤ (2731178416983 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107118705840149061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13644881350983 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (54579525403931 / 100000000000000 : ℝ)) ≤ (2731178416983 / 20000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_326 : ∀ t : ℝ, (1525209391779 / 5120000000000 : ℝ) < t → t ≤ (2387998646983 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-162294879803053812952011899 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2387998646983 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_327
  have hV : (17007579218109213826963102527057939 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1525209391779 / 5120000000000 : ℝ) := by norm_num
    refine le_trans V_pt_326 (Vfield_monotoneOn (show (1525209391779 / 5120000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1525209391779 / 5120000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_327 : (8513226027902146828481210222842609 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (2387998646983 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2387998646983 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (27317569020361 / 50000000000000 : ℝ) ≤ Real.sqrt (2387998646983 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2387998646983 / 8000000000000 : ℝ) ≤ (54635138040723 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (54635138040723 / 100000000000000 : ℝ) = (100000000000000 / 54635138040723 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27317569020361 / 50000000000000 : ℝ) = (3750000000000 / 27317569020361 : ℝ) := by norm_num
  have hL1 : (13060481093629 / 50000000000000 : ℝ) ≤ Real.log (1 + (2387998646983 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2387998646983 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-119031703346927 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (18211712680241 / 71317245583900 : ℝ) ≤ (125009413087319 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (54635138040723 / 100000000000000 : ℝ) ≤ (125009413087319 / 250000000000000 : ℝ) := by
    have hw : (1139517367517 / 1000000000000 : ℝ) ≤ Real.sqrt (1 + (54635138040723 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (54635138040723 / 100000000000000 : ℝ) / (1 + (1139517367517 / 1000000000000 : ℝ)) = (18211712680241 / 71317245583900 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107075867444562061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 54635138040723 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 54635138040723 : ℝ) = (54635138040723 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 27317569020361 : ℝ) ≤ (136421637782343 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107075867444562061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (54635138040723 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27317569020361 / 50000000000000 : ℝ)) ≤ (136421637782343 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_327 : ∀ t : ℝ, (2387998646983 / 8000000000000 : ℝ) < t → t ≤ (38285721908981 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-162116422049407826654517537 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (38285721908981 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_328
  have hV : (8513226027902146828481210222842609 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2387998646983 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_327 (Vfield_monotoneOn (show (2387998646983 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2387998646983 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_328 : (17045307893612258418266643822271749 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (38285721908981 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (38285721908981 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (54690694127421 / 100000000000000 : ℝ) ≤ Real.sqrt (38285721908981 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (38285721908981 / 128000000000000 : ℝ) ≤ (27345347063711 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (27345347063711 / 50000000000000 : ℝ) = (50000000000000 / 27345347063711 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (54690694127421 / 100000000000000 : ℝ) = (2500000000000 / 18230231375807 : ℝ) := by norm_num
  have hL1 : (26167726116083 / 100000000000000 : ℝ) ≤ Real.log (1 + (38285721908981 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((38285721908981 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-59416095620843 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54690694127422 / 213978384021441 : ℝ) ≤ (50046540057447 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (27345347063711 / 50000000000000 : ℝ) ≤ (50046540057447 / 100000000000000 : ℝ) := by
    have hw : (113978384021441 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (27345347063711 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (27345347063711 / 50000000000000 : ℝ) / (1 + (113978384021441 / 100000000000000 : ℝ)) = (54690694127422 / 213978384021441 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (107033092622042661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 27345347063711 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 27345347063711 : ℝ) = (27345347063711 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 18230231375807 : ℝ) ≤ (68142383965387 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (107033092622042661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (27345347063711 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (54690694127421 / 100000000000000 : ℝ)) ≤ (68142383965387 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_328 : ∀ t : ℝ, (38285721908981 / 128000000000000 : ℝ) < t → t ≤ (19181732733117 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-161938954440889412058599037 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19181732733117 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_329
  have hV : (17045307893612258418266643822271749 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (38285721908981 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_328 (Vfield_monotoneOn (show (38285721908981 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (38285721908981 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_329 : (4266036693827063624705506034102143 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (19181732733117 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19181732733117 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (13686548459047 / 25000000000000 : ℝ) ≤ Real.sqrt (19181732733117 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19181732733117 / 64000000000000 : ℝ) ≤ (54746193836189 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (54746193836189 / 100000000000000 : ℝ) = (100000000000000 / 54746193836189 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13686548459047 / 25000000000000 : ℝ) = (1875000000000 / 13686548459047 : ℝ) := by norm_num
  have hL1 : (327680852331 / 1250000000000 : ℝ) ≤ Real.log (1 + (19181732733117 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19181732733117 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-118633076394799 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54746193836189 / 214005025062711 : ℝ) ≤ (2504462574941 / 10000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (54746193836189 / 100000000000000 : ℝ) ≤ (2504462574941 / 5000000000000 : ℝ) := by
    have hw : (114005025062711 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (54746193836189 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (54746193836189 / 100000000000000 : ℝ) / (1 + (114005025062711 / 100000000000000 : ℝ)) = (54746193836189 / 214005025062711 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106990381180669661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 54746193836189 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 54746193836189 : ℝ) = (54746193836189 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 13686548459047 : ℝ) ≤ (136148309225601 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106990381180669661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (54746193836189 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13686548459047 / 25000000000000 : ℝ)) ≤ (136148309225601 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_329 : ∀ t : ℝ, (19181732733117 / 64000000000000 : ℝ) < t → t ≤ (38441209023487 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-161762455986661219665223539 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (38441209023487 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_330
  have hV : (4266036693827063624705506034102143 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19181732733117 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_329 (Vfield_monotoneOn (show (19181732733117 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19181732733117 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_330 : (2135371093060119750660953131810241 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (38441209023487 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (38441209023487 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (6850204667289 / 12500000000000 : ℝ) ≤ Real.sqrt (38441209023487 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (38441209023487 / 128000000000000 : ℝ) ≤ (54801637338313 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (54801637338313 / 100000000000000 : ℝ) = (100000000000000 / 54801637338313 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6850204667289 / 12500000000000 : ℝ) = (312500000000 / 2283401555763 : ℝ) := by norm_num
  have hL1 : (3282648552359 / 12500000000000 : ℝ) ≤ Real.log (1 + (38441209023487 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((38441209023487 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-118434357227409 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54801637338313 / 214031659879877 : ℝ) ≤ (125329749375073 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (54801637338313 / 100000000000000 : ℝ) ≤ (125329749375073 / 250000000000000 : ℝ) := by
    have hw : (114031659879877 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (54801637338313 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (54801637338313 / 100000000000000 : ℝ) / (1 + (114031659879877 / 100000000000000 : ℝ)) = (54801637338313 / 214031659879877 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106947732929460461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 54801637338313 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 54801637338313 : ℝ) = (54801637338313 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (312500000000 / 2283401555763 : ℝ) ≤ (136012259612453 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106947732929460461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (54801637338313 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6850204667289 / 12500000000000 : ℝ)) ≤ (136012259612453 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_330 : ∀ t : ℝ, (38441209023487 / 128000000000000 : ℝ) < t → t ≤ (1925947629037 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-4039672665620063722605397 / 2500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1925947629037 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_331
  have hV : (2135371093060119750660953131810241 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (38441209023487 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_330 (Vfield_monotoneOn (show (38441209023487 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (38441209023487 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_331 : (3420354768906634064185340779843267 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (1925947629037 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1925947629037 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (10971404960843 / 20000000000000 : ℝ) ≤ Real.sqrt (1925947629037 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1925947629037 / 6400000000000 : ℝ) ≤ (6857128100527 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6857128100527 / 12500000000000 : ℝ) = (12500000000000 / 6857128100527 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (10971404960843 / 20000000000000 : ℝ) = (1500000000000 / 10971404960843 : ℝ) := by norm_num
  have hL1 : (26307886833657 / 100000000000000 : ℝ) ≤ Real.log (1 + (1925947629037 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1925947629037 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-118236032170051 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54857024804216 / 214058288477297 : ℝ) ≤ (250872425005617 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6857128100527 / 12500000000000 : ℝ) ≤ (250872425005617 / 500000000000000 : ℝ) := by
    have hw : (114058288477297 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (6857128100527 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (6857128100527 / 12500000000000 : ℝ) / (1 + (114058288477297 / 100000000000000 : ℝ)) = (54857024804216 / 214058288477297 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106905147678366261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 6857128100527 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 6857128100527 : ℝ) = (6857128100527 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 10971404960843 : ℝ) ≤ (16984577131413 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106905147678366261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6857128100527 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (10971404960843 / 20000000000000 : ℝ)) ≤ (16984577131413 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_331 : ∀ t : ℝ, (1925947629037 / 6400000000000 : ℝ) < t → t ≤ (19337219847623 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-40309644804039018905147571 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19337219847623 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_332
  have hV : (3420354768906634064185340779843267 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1925947629037 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_331 (Vfield_monotoneOn (show (1925947629037 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1925947629037 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_332 : (8569666804983469378804560926494451 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (19337219847623 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19337219847623 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (27483816152379 / 50000000000000 : ℝ) ≤ Real.sqrt (19337219847623 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19337219847623 / 64000000000000 : ℝ) ≤ (54967632304759 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (54967632304759 / 100000000000000 : ℝ) = (100000000000000 / 54967632304759 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27483816152379 / 50000000000000 : ℝ) = (1250000000000 / 9161272050793 : ℝ) := by norm_num
  have hL1 : (26401218291841 / 100000000000000 : ℝ) ≤ Real.log (1 + (19337219847623 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19337219847623 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-117840558154097 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (54967632304759 / 214111527030318 : ℝ) ≤ (251297336292677 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (54967632304759 / 100000000000000 : ℝ) ≤ (251297336292677 / 500000000000000 : ℝ) := by
    have hw : (57055763515159 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (54967632304759 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (54967632304759 / 100000000000000 : ℝ) / (1 + (57055763515159 / 50000000000000 : ℝ)) = (54967632304759 / 214111527030318 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106820165420954261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 54967632304759 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 54967632304759 : ℝ) = (54967632304759 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 9161272050793 : ℝ) ≤ (135606544995841 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106820165420954261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (54967632304759 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27483816152379 / 50000000000000 : ℝ)) ≤ (135606544995841 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_332 : ∀ t : ℝ, (19337219847623 / 64000000000000 : ℝ) < t → t ≤ (4853740851219 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-160893828117652676139418429 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4853740851219 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_333
  have hV : (8569666804983469378804560926494451 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19337219847623 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_332 (Vfield_monotoneOn (show (19337219847623 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19337219847623 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_333 : (4294206603791065052433944564536301 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (4853740851219 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4853740851219 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (13769504421029 / 25000000000000 : ℝ) ≤ Real.sqrt (4853740851219 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4853740851219 / 16000000000000 : ℝ) ≤ (55078017684117 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (55078017684117 / 100000000000000 : ℝ) = (100000000000000 / 55078017684117 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13769504421029 / 25000000000000 : ℝ) = (1875000000000 / 13769504421029 : ℝ) := by norm_num
  have hL1 : (26494462723631 / 100000000000000 : ℝ) ≤ Real.log (1 + (4853740851219 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4853740851219 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-58723320988147 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (55078017684117 / 214164740756557 : ℝ) ≤ (12586049943257 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (55078017684117 / 100000000000000 : ℝ) ≤ (12586049943257 / 25000000000000 : ℝ) := by
    have hw : (114164740756557 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (55078017684117 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (55078017684117 / 100000000000000 : ℝ) / (1 + (114164740756557 / 100000000000000 : ℝ)) = (55078017684117 / 214164740756557 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106735432906461661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 55078017684117 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 55078017684117 : ℝ) = (55078017684117 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 13769504421029 : ℝ) ≤ (33834519255253 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106735432906461661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (55078017684117 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13769504421029 / 25000000000000 : ℝ)) ≤ (33834519255253 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_333 : ∀ t : ℝ, (4853740851219 / 16000000000000 : ℝ) < t → t ≤ (19492706962129 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-8027626034599402274009817 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19492706962129 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_334
  have hV : (4294206603791065052433944564536301 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4853740851219 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_333 (Vfield_monotoneOn (show (4853740851219 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4853740851219 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_334 : (17214252600782277912246694731667663 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (19492706962129 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19492706962129 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (55188182275127 / 100000000000000 : ℝ) ≤ Real.sqrt (19492706962129 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19492706962129 / 64000000000000 : ℝ) ≤ (6898522784391 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (6898522784391 / 12500000000000 : ℝ) = (12500000000000 / 6898522784391 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (55188182275127 / 100000000000000 : ℝ) = (7500000000000 / 55188182275127 : ℝ) := by norm_num
  have hL1 : (26587620291171 / 100000000000000 : ℝ) ≤ Real.log (1 + (19492706962129 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19492706962129 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-117054271411613 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (6132020252792 / 23801992187857 : ℝ) ≤ (50428684032053 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (6898522784391 / 12500000000000 : ℝ) ≤ (50428684032053 / 100000000000000 : ℝ) := by
    have hw : (114217929690713 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (6898522784391 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (6898522784391 / 12500000000000 : ℝ) / (1 + (114217929690713 / 100000000000000 : ℝ)) = (6132020252792 / 23801992187857 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106650948647436661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 6898522784391 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 6898522784391 : ℝ) = (6898522784391 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 55188182275127 : ℝ) ≤ (27014239462003 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106650948647436661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (6898522784391 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (55188182275127 / 100000000000000 : ℝ)) ≤ (27014239462003 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_334 : ∀ t : ℝ, (19492706962129 / 64000000000000 : ℝ) < t → t ≤ (9785225259691 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-160214534441228731103931483 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9785225259691 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_335
  have hV : (17214252600782277912246694731667663 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19492706962129 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_334 (Vfield_monotoneOn (show (19492706962129 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19492706962129 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_335 : (4312903126152924696621812474085153 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (9785225259691 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9785225259691 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (13824531849337 / 25000000000000 : ℝ) ≤ Real.sqrt (9785225259691 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9785225259691 / 32000000000000 : ℝ) ≤ (55298127397349 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (55298127397349 / 100000000000000 : ℝ) = (100000000000000 / 55298127397349 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13824531849337 / 25000000000000 : ℝ) = (1875000000000 / 13824531849337 : ℝ) := by norm_num
  have hL1 : (533613823123 / 2000000000000 : ℝ) ≤ Real.log (1 + (9785225259691 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9785225259691 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-58331717189183 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (55298127397349 / 214271093867405 : ℝ) ≤ (50512921508733 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (55298127397349 / 100000000000000 : ℝ) ≤ (50512921508733 / 100000000000000 : ℝ) := by
    have hw : (22854218773481 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (55298127397349 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (55298127397349 / 100000000000000 : ℝ) / (1 + (22854218773481 / 20000000000000 : ℝ)) = (55298127397349 / 214271093867405 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106566711170756661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 55298127397349 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 55298127397349 : ℝ) = (55298127397349 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 13824531849337 : ℝ) ≤ (2696117805271 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106566711170756661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (55298127397349 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13824531849337 / 25000000000000 : ℝ)) ≤ (2696117805271 / 20000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_335 : ∀ t : ℝ, (9785225259691 / 32000000000000 : ℝ) < t → t ≤ (3929638815327 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-79939877931154070879401907 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3929638815327 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_336
  have hV : (4312903126152924696621812474085153 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9785225259691 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_335 (Vfield_monotoneOn (show (9785225259691 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9785225259691 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_336 : (17288906461614033744788362717589481 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (3929638815327 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3929638815327 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (55407854357249 / 100000000000000 : ℝ) ≤ Real.sqrt (3929638815327 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3929638815327 / 12800000000000 : ℝ) ≤ (221631417429 / 400000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (221631417429 / 400000000000 : ℝ) = (400000000000 / 221631417429 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (55407854357249 / 100000000000000 : ℝ) = (7500000000000 / 55407854357249 : ℝ) := by norm_num
  have hL1 : (26773675479809 / 100000000000000 : ℝ) ≤ Real.log (1 + (3929638815327 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3929638815327 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-116274118935973 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (55407854357250 / 214324233321173 : ℝ) ≤ (252984568310319 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (221631417429 / 400000000000 : ℝ) ≤ (252984568310319 / 500000000000000 : ℝ) := by
    have hw : (114324233321173 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (221631417429 / 400000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (221631417429 / 400000000000 : ℝ) / (1 + (114324233321173 / 100000000000000 : ℝ)) = (55407854357250 / 214324233321173 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106482719017425861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (400000000000 / 221631417429 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (400000000000 / 221631417429 : ℝ) = (221631417429 / 400000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 55407854357249 : ℝ) ≤ (4204441890499 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106482719017425861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (221631417429 / 400000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (55407854357249 / 100000000000000 : ℝ)) ≤ (4204441890499 / 31250000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_336 : ∀ t : ℝ, (3929638815327 / 12800000000000 : ℝ) < t → t ≤ (616435551059 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-159548079474892478463026193 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (616435551059 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_337
  have hV : (17288906461614033744788362717589481 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3929638815327 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_336 (Vfield_monotoneOn (show (3929638815327 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3929638815327 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_337 : (8663067401975713687313993538509417 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (616435551059 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (616435551059 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (27758682224193 / 50000000000000 : ℝ) ≤ Real.sqrt (616435551059 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (616435551059 / 2000000000000 : ℝ) ≤ (55517364448387 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (55517364448387 / 100000000000000 : ℝ) = (100000000000000 / 55517364448387 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (27758682224193 / 50000000000000 : ℝ) = (1250000000000 / 9252894074731 : ℝ) := by norm_num
  have hL1 : (26866573422937 / 100000000000000 : ℝ) ≤ Real.log (1 + (616435551059 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((616435551059 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4635452531311 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (55517364448387 / 214377348086476 : ℝ) ≤ (253403309685493 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (55517364448387 / 100000000000000 : ℝ) ≤ (253403309685493 / 500000000000000 : ℝ) := by
    have hw : (28594337021619 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (55517364448387 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (55517364448387 / 100000000000000 : ℝ) / (1 + (28594337021619 / 25000000000000 : ℝ)) = (55517364448387 / 214377348086476 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106398970742391061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 55517364448387 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 55517364448387 : ℝ) = (55517364448387 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 9252894074731 : ℝ) ≤ (134279932831539 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106398970742391061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (55517364448387 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (27758682224193 / 50000000000000 : ℝ)) ≤ (134279932831539 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_337 : ∀ t : ℝ, (616435551059 / 2000000000000 : ℝ) < t → t ≤ (19803681191141 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-159219406981732694288164469 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19803681191141 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_338
  have hV : (8663067401975713687313993538509417 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (616435551059 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_337 (Vfield_monotoneOn (show (616435551059 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (616435551059 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_338 : (17363297861020659534642897639222327 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (19803681191141 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19803681191141 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (55626658951583 / 100000000000000 : ℝ) ≤ Real.sqrt (19803681191141 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19803681191141 / 64000000000000 : ℝ) ≤ (1738333092237 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1738333092237 / 3125000000000 : ℝ) = (3125000000000 / 1738333092237 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (55626658951583 / 100000000000000 : ℝ) = (7500000000000 / 55626658951583 : ℝ) := by norm_num
  have hL1 : (13479692572939 / 50000000000000 : ℝ) ≤ Real.log (1 + (19803681191141 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19803681191141 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-57750002876941 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (4635554912632 / 17869203183141 : ℝ) ≤ (253820838825699 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1738333092237 / 3125000000000 : ℝ) ≤ (253820838825699 / 500000000000000 : ℝ) := by
    have hw : (28607609549423 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (1738333092237 / 3125000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1738333092237 / 3125000000000 : ℝ) / (1 + (28607609549423 / 25000000000000 : ℝ)) = (4635554912632 / 17869203183141 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106315464914349861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 1738333092237 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 1738333092237 : ℝ) = (1738333092237 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 55626658951583 : ℝ) ≤ (67009626150389 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106315464914349861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1738333092237 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (55626658951583 / 100000000000000 : ℝ)) ≤ (67009626150389 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_338 : ∀ t : ℝ, (19803681191141 / 64000000000000 : ℝ) < t → t ≤ (9940712374197 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-79446823270691347587634167 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9940712374197 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_339
  have hV : (17363297861020659534642897639222327 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19803681191141 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_338 (Vfield_monotoneOn (show (19803681191141 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19803681191141 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_339 : (3480079191896892922472871366664149 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (9940712374197 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9940712374197 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (11147147827021 / 20000000000000 : ℝ) ≤ Real.sqrt (9940712374197 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9940712374197 / 32000000000000 : ℝ) ≤ (27867869567553 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (27867869567553 / 50000000000000 : ℝ) = (50000000000000 / 27867869567553 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (11147147827021 / 20000000000000 : ℝ) = (1500000000000 / 11147147827021 : ℝ) := by norm_num
  have hL1 : (27052110808527 / 100000000000000 : ℝ) ≤ Real.log (1 + (9940712374197 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9940712374197 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4604607392763 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (55735739135106 / 214483503689119 : ℝ) ≤ (254237162819609 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (27867869567553 / 50000000000000 : ℝ) ≤ (254237162819609 / 500000000000000 : ℝ) := by
    have hw : (114483503689119 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (27867869567553 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (27867869567553 / 50000000000000 : ℝ) / (1 + (114483503689119 / 100000000000000 : ℝ)) = (55735739135106 / 214483503689119 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106232200115567861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 27867869567553 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 27867869567553 : ℝ) = (27867869567553 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 11147147827021 : ℝ) ≤ (133760084136857 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106232200115567861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (27867869567553 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (11147147827021 / 20000000000000 : ℝ)) ≤ (133760084136857 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_339 : ∀ t : ℝ, (9940712374197 / 32000000000000 : ℝ) < t → t ≤ (200369118629 / 640000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15825052301468688489416007 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (200369118629 / 640000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_340
  have hV : (3480079191896892922472871366664149 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9940712374197 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_339 (Vfield_monotoneOn (show (9940712374197 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9940712374197 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_340 : (17474398573770267253538965817549363 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (200369118629 / 640000000000 : ℝ) := by
  have hp : (0 : ℝ) < (200369118629 / 640000000000 : ℝ) := by norm_num
  have hs1 : (55953261554427 / 100000000000000 : ℝ) ≤ Real.sqrt (200369118629 / 640000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (200369118629 / 640000000000 : ℝ) ≤ (13988315388607 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13988315388607 / 25000000000000 : ℝ) = (25000000000000 / 13988315388607 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (55953261554427 / 100000000000000 : ℝ) = (2500000000000 / 18651087184809 : ℝ) := by norm_num
  have hL1 : (13618652295159 / 50000000000000 : ℝ) ≤ Real.log (1 + (200369118629 / 640000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((200369118629 / 640000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-114349957271821 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (13988315388607 / 53647390237352 : ℝ) ≤ (255066223389467 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13988315388607 / 25000000000000 : ℝ) ≤ (255066223389467 / 500000000000000 : ℝ) := by
    have hw : (3580923779669 / 3125000000000 : ℝ) ≤ Real.sqrt (1 + (13988315388607 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (13988315388607 / 25000000000000 : ℝ) / (1 + (3580923779669 / 3125000000000 : ℝ)) = (13988315388607 / 53647390237352 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (106066388001596261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 13988315388607 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 13988315388607 : ℝ) = (13988315388607 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 18651087184809 : ℝ) ≤ (133246226834473 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (106066388001596261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13988315388607 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (55953261554427 / 100000000000000 : ℝ)) ≤ (133246226834473 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_340 : ∀ t : ℝ, (200369118629 / 640000000000 : ℝ) < t → t ≤ (10096199488703 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-157618081128067685541990617 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10096199488703 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_341
  have hV : (17474398573770267253538965817549363 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (200369118629 / 640000000000 : ℝ) := by norm_num
    refine le_trans V_pt_340 (Vfield_monotoneOn (show (200369118629 / 640000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (200369118629 / 640000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_341 : (4387036301656802245203605511577629 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (10096199488703 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10096199488703 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (14042485401941 / 25000000000000 : ℝ) ≤ Real.sqrt (10096199488703 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10096199488703 / 32000000000000 : ℝ) ≤ (11233988321553 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (11233988321553 / 20000000000000 : ℝ) = (20000000000000 / 11233988321553 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14042485401941 / 25000000000000 : ℝ) = (1875000000000 / 14042485401941 : ℝ) := by norm_num
  have hL1 : (27422156038623 / 100000000000000 : ℝ) ≤ Real.log (1 + (10096199488703 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10096199488703 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-22718108203021 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1248220924617 / 4771011558670 : ℝ) ≤ (255890546781719 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (11233988321553 / 20000000000000 : ℝ) ≤ (255890546781719 / 500000000000000 : ℝ) := by
    have hw : (2293910402803 / 2000000000000 : ℝ) ≤ Real.sqrt (1 + (11233988321553 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (11233988321553 / 20000000000000 : ℝ) / (1 + (2293910402803 / 2000000000000 : ℝ)) = (1248220924617 / 4771011558670 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (105901523323145861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 11233988321553 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 11233988321553 : ℝ) = (11233988321553 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 14042485401941 : ℝ) ≤ (132738246711171 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (105901523323145861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (11233988321553 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14042485401941 / 25000000000000 : ℝ)) ≤ (132738246711171 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_341 : ∀ t : ℝ, (10096199488703 / 32000000000000 : ℝ) < t → t ≤ (2543485761489 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-156995763215830517032663657 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2543485761489 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_342
  have hV : (4387036301656802245203605511577629 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10096199488703 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_341 (Vfield_monotoneOn (show (10096199488703 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10096199488703 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_342 : (4405409594027086056522512674493099 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (2543485761489 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2543485761489 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (14096447251571 / 25000000000000 : ℝ) ≤ Real.sqrt (2543485761489 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2543485761489 / 8000000000000 : ℝ) ≤ (11277157801257 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (11277157801257 / 20000000000000 : ℝ) = (20000000000000 / 11277157801257 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14096447251571 / 25000000000000 : ℝ) = (1875000000000 / 14096447251571 : ℝ) := by norm_num
  have hL1 : (1104266656669 / 4000000000000 : ℝ) ≤ Real.log (1 + (2543485761489 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2543485761489 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-112836848449557 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (56385789006285 / 214801381532894 : ℝ) ≤ (256710187354019 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (11277157801257 / 20000000000000 : ℝ) ≤ (256710187354019 / 500000000000000 : ℝ) := by
    have hw : (57400690766447 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (11277157801257 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (11277157801257 / 20000000000000 : ℝ) / (1 + (57400690766447 / 50000000000000 : ℝ)) = (56385789006285 / 214801381532894 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (105737595208685861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 11277157801257 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 11277157801257 : ℝ) = (11277157801257 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 14096447251571 : ℝ) ≤ (33059008144719 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (105737595208685861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (11277157801257 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14096447251571 / 25000000000000 : ℝ)) ≤ (33059008144719 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_342 : ∀ t : ℝ, (2543485761489 / 8000000000000 : ℝ) < t → t ≤ (10251686603209 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-156383070188402959513083821 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10251686603209 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_343
  have hV : (4405409594027086056522512674493099 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2543485761489 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_342 (Vfield_monotoneOn (show (2543485761489 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2543485761489 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_343 : (1105930034965270862335134439641981 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (10251686603209 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10251686603209 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (3537550829749 / 6250000000000 : ℝ) ≤ Real.sqrt (10251686603209 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10251686603209 / 32000000000000 : ℝ) ≤ (11320162655197 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (11320162655197 / 20000000000000 : ℝ) = (20000000000000 / 11320162655197 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3537550829749 / 6250000000000 : ℝ) = (468750000000 / 3537550829749 : ℝ) := by norm_num
  have hL1 : (27790836980927 / 100000000000000 : ℝ) ≤ Real.log (1 + (10251686603209 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10251686603209 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-11208879394171 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (56600813275985 / 214907145397938 : ℝ) ≤ (2011915612983 / 7812500000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (11320162655197 / 20000000000000 : ℝ) ≤ (2011915612983 / 3906250000000 : ℝ) := by
    have hw : (57453572698969 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (11320162655197 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (11320162655197 / 20000000000000 : ℝ) / (1 + (57453572698969 / 50000000000000 : ℝ)) = (56600813275985 / 214907145397938 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (105574592987124861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 11320162655197 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 11320162655197 : ℝ) = (11320162655197 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (468750000000 / 3537550829749 : ℝ) ≤ (6586973808621 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (105574592987124861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (11320162655197 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3537550829749 / 6250000000000 : ℝ)) ≤ (6586973808621 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_343 : ∀ t : ℝ, (10251686603209 / 32000000000000 : ℝ) < t → t ≤ (5164715080231 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-3894488810187062461045161 / 2500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5164715080231 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_344
  have hV : (1105930034965270862335134439641981 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10251686603209 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_343 (Vfield_monotoneOn (show (10251686603209 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10251686603209 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_344 : (4441968548490323596214033815824081 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (5164715080231 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5164715080231 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (14203755940649 / 25000000000000 : ℝ) ≤ Real.sqrt (5164715080231 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5164715080231 / 16000000000000 : ℝ) ≤ (56815023762597 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (56815023762597 / 100000000000000 : ℝ) = (100000000000000 / 56815023762597 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14203755940649 / 25000000000000 : ℝ) = (1875000000000 / 14203755940649 : ℝ) := by norm_num
  have hL1 : (27974668980601 / 100000000000000 : ℝ) ≤ Real.log (1 + (5164715080231 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5164715080231 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-111346293765611 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (18938341254199 / 71670937334778 : ℝ) ≤ (64583908121083 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (56815023762597 / 100000000000000 : ℝ) ≤ (64583908121083 / 125000000000000 : ℝ) := by
    have hw : (57506406002167 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (56815023762597 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (56815023762597 / 100000000000000 : ℝ) / (1 + (57506406002167 / 50000000000000 : ℝ)) = (18938341254199 / 71670937334778 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (105412506182623261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 56815023762597 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 56815023762597 : ℝ) = (56815023762597 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 14203755940649 : ℝ) ≤ (131248472051483 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (105412506182623261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (56815023762597 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14203755940649 / 25000000000000 : ℝ)) ≤ (131248472051483 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_344 : ∀ t : ℝ, (5164715080231 / 16000000000000 : ℝ) < t → t ≤ (1310614659371 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-30919689757315595021526289 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1310614659371 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_345
  have hV : (4441968548490323596214033815824081 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5164715080231 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_344 (Vfield_monotoneOn (show (5164715080231 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5164715080231 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_345 : (8956562685825835201561221890781563 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1310614659371 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1310614659371 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (28620519948227 / 50000000000000 : ℝ) ≤ Real.sqrt (1310614659371 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1310614659371 / 4000000000000 : ℝ) ≤ (11448207979291 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (11448207979291 / 20000000000000 : ℝ) = (20000000000000 / 11448207979291 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (28620519948227 / 50000000000000 : ℝ) = (3750000000000 / 28620519948227 : ℝ) := by norm_num
  have hL1 : (2834132224953 / 10000000000000 : ℝ) ≤ Real.log (1 + (1310614659371 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1310614659371 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-109877630707033 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (11448207979291 / 43044770902248 : ℝ) ≤ (129971487029269 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (11448207979291 / 20000000000000 : ℝ) ≤ (129971487029269 / 250000000000000 : ℝ) := by
    have hw : (2880596362781 / 2500000000000 : ℝ) ≤ Real.sqrt (1 + (11448207979291 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (11448207979291 / 20000000000000 : ℝ) / (1 + (2880596362781 / 2500000000000 : ℝ)) = (11448207979291 / 43044770902248 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (105091037867782061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 11448207979291 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 11448207979291 : ℝ) = (11448207979291 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 28620519948227 : ℝ) ≤ (130282712468499 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (105091037867782061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (11448207979291 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (28620519948227 / 50000000000000 : ℝ)) ≤ (130282712468499 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_345 : ∀ t : ℝ, (1310614659371 / 4000000000000 : ℝ) < t → t ≤ (5320202194737 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-38362399628353938704632973 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5320202194737 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_346
  have hV : (8956562685825835201561221890781563 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1310614659371 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_345 (Vfield_monotoneOn (show (1310614659371 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1310614659371 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_346 : (18057410642974650858525235162785467 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (5320202194737 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5320202194737 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (57663908744643 / 100000000000000 : ℝ) ≤ Real.sqrt (5320202194737 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5320202194737 / 16000000000000 : ℝ) ≤ (14415977186161 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (14415977186161 / 25000000000000 : ℝ) = (25000000000000 / 14415977186161 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (57663908744643 / 100000000000000 : ℝ) = (2500000000000 / 19221302914881 : ℝ) := by norm_num
  have hL1 : (448541188779 / 1562500000000 : ℝ) ≤ Real.log (1 + (5320202194737 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5320202194737 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-108430225530167 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (28831954372322 / 107717255590747 : ℝ) ≤ (261532612517121 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (14415977186161 / 25000000000000 : ℝ) ≤ (261532612517121 / 500000000000000 : ℝ) := by
    have hw : (57717255590747 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (14415977186161 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (14415977186161 / 25000000000000 : ℝ) / (1 + (57717255590747 / 50000000000000 : ℝ)) = (28831954372322 / 107717255590747 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (104773110176065461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 14415977186161 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 14415977186161 : ℝ) = (14415977186161 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 19221302914881 : ℝ) ≤ (129337963323317 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (104773110176065461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (14415977186161 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (57663908744643 / 100000000000000 : ℝ)) ≤ (129337963323317 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_346 : ∀ t : ℝ, (5320202194737 / 16000000000000 : ℝ) < t → t ≤ (539794575199 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-152330590491024195255010763 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (539794575199 / 1600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_347
  have hV : (18057410642974650858525235162785467 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5320202194737 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_346 (Vfield_monotoneOn (show (5320202194737 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5320202194737 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_347 : (18200748157775462716590733974762593 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (539794575199 / 1600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (539794575199 / 1600000000000 : ℝ) := by norm_num
  have hs1 : (58083699047097 / 100000000000000 : ℝ) ≤ Real.sqrt (539794575199 / 1600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (539794575199 / 1600000000000 : ℝ) ≤ (29041849523549 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (29041849523549 / 50000000000000 : ℝ) = (50000000000000 / 29041849523549 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (58083699047097 / 100000000000000 : ℝ) = (2500000000000 / 19361233015699 : ℝ) := by norm_num
  have hL1 : (14535310114137 / 50000000000000 : ℝ) ≤ Real.log (1 + (539794575199 / 1600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((539794575199 / 1600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-107003471618663 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (58083699047098 / 215644784123599 : ℝ) ≤ (32888116775159 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (29041849523549 / 50000000000000 : ℝ) ≤ (32888116775159 / 62500000000000 : ℝ) := by
    have hw : (115644784123599 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (29041849523549 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (29041849523549 / 50000000000000 : ℝ) / (1 + (115644784123599 / 100000000000000 : ℝ)) = (58083699047098 / 215644784123599 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (104458645839235261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 29041849523549 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 29041849523549 : ℝ) = (29041849523549 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 19361233015699 : ℝ) ≤ (128413473666421 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (104458645839235261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (29041849523549 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (58083699047097 / 100000000000000 : ℝ)) ≤ (128413473666421 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_347 : ∀ t : ℝ, (539794575199 / 1600000000000 : ℝ) < t → t ≤ (5475689309243 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-151239355875566935579051377 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5475689309243 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_348
  have hV : (18200748157775462716590733974762593 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (539794575199 / 1600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_347 (Vfield_monotoneOn (show (539794575199 / 1600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (539794575199 / 1600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_348 : (573223609595758244806931995159923 / 156250000000000000000000000000000 : ℝ) ≤ Vfield (5475689309243 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5475689309243 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (1828139908667 / 3125000000000 : ℝ) ≤ Real.sqrt (5475689309243 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5475689309243 / 16000000000000 : ℝ) ≤ (11700095415469 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (11700095415469 / 20000000000000 : ℝ) = (20000000000000 / 11700095415469 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1828139908667 / 3125000000000 : ℝ) = (234375000000 / 1828139908667 : ℝ) := by norm_num
  have hL1 : (29433284333393 / 100000000000000 : ℝ) ≤ Real.log (1 + (5475689309243 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5475689309243 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-52798393978497 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (58500477077345 / 215854675426919 : ℝ) ≤ (264660312044253 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (11700095415469 / 20000000000000 : ℝ) ≤ (264660312044253 / 500000000000000 : ℝ) := by
    have hw : (115854675426919 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (11700095415469 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (11700095415469 / 20000000000000 : ℝ) / (1 + (115854675426919 / 100000000000000 : ℝ)) = (58500477077345 / 215854675426919 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (104147570270639061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 11700095415469 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 11700095415469 : ℝ) = (11700095415469 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (234375000000 / 1828139908667 : ℝ) ≤ (127508529596187 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (104147570270639061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (11700095415469 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1828139908667 / 3125000000000 : ℝ)) ≤ (127508529596187 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_348 : ∀ t : ℝ, (5475689309243 / 16000000000000 : ℝ) < t → t ≤ (86772388539 / 250000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-234647025536773059855943 / 156250000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (86772388539 / 250000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_349
  have hV : (573223609595758244806931995159923 / 156250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5475689309243 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_348 (Vfield_monotoneOn (show (5475689309243 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5475689309243 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_349 : (1155290609173111966209660043211279 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (86772388539 / 250000000000 : ℝ) := by
  have hp : (0 : ℝ) < (86772388539 / 250000000000 : ℝ) := by norm_num
  have hs1 : (3682144172791 / 6250000000000 : ℝ) ≤ Real.sqrt (86772388539 / 250000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (86772388539 / 250000000000 : ℝ) ≤ (58914306764657 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (58914306764657 / 100000000000000 : ℝ) = (100000000000000 / 58914306764657 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3682144172791 / 6250000000000 : ℝ) = (468750000000 / 3682144172791 : ℝ) := by norm_num
  have hL1 : (29794637937267 / 100000000000000 : ℝ) ≤ Real.log (1 + (86772388539 / 250000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((86772388539 / 250000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-20841923541971 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (58914306764657 / 216064187161932 : ℝ) ≤ (66549776554851 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (58914306764657 / 100000000000000 : ℝ) ≤ (66549776554851 / 125000000000000 : ℝ) := by
    have hw : (29016046790483 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (58914306764657 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (58914306764657 / 100000000000000 : ℝ) / (1 + (29016046790483 / 25000000000000 : ℝ)) = (58914306764657 / 216064187161932 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (103839811435608861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 58914306764657 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 58914306764657 : ℝ) = (58914306764657 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (468750000000 / 3682144172791 : ℝ) ≤ (253244903883 / 2000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (103839811435608861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (58914306764657 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3682144172791 / 6250000000000 : ℝ)) ≤ (253244903883 / 2000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_349 : ∀ t : ℝ, (86772388539 / 250000000000 : ℝ) < t → t ≤ (11190582883251 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-148128198200058906021927567 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11190582883251 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_350
  have hV : (1155290609173111966209660043211279 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (86772388539 / 250000000000 : ℝ) := by norm_num
    refine le_trans V_pt_349 (Vfield_monotoneOn (show (86772388539 / 250000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (86772388539 / 250000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_350 : (18560460520479399657124196974776393 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (11190582883251 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11190582883251 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (59135920987297 / 100000000000000 : ℝ) ≤ Real.sqrt (11190582883251 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11190582883251 / 32000000000000 : ℝ) ≤ (29567960493649 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (29567960493649 / 50000000000000 : ℝ) = (50000000000000 / 29567960493649 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (59135920987297 / 100000000000000 : ℝ) = (7500000000000 / 59135920987297 : ℝ) := by norm_num
  have hL1 : (3748582248421 / 12500000000000 : ℝ) ≤ Real.log (1 + (11190582883251 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11190582883251 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-103470633081371 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (59135920987298 / 216176835690321 : ℝ) ≤ (53404175156259 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (29567960493649 / 50000000000000 : ℝ) ≤ (53404175156259 / 100000000000000 : ℝ) := by
    have hw : (116176835690321 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (29567960493649 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (29567960493649 / 50000000000000 : ℝ) / (1 + (116176835690321 / 100000000000000 : ℝ)) = (59135920987298 / 216176835690321 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (103675457523230661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 29567960493649 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 29567960493649 : ℝ) = (29567960493649 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 59135920987297 : ℝ) ≤ (1009223656643 / 8000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (103675457523230661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (29567960493649 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (59135920987297 / 100000000000000 : ℝ)) ≤ (1009223656643 / 8000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_350 : ∀ t : ℝ, (11190582883251 / 32000000000000 : ℝ) < t → t ≤ (1127430003351 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-146960207351878801487500907 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1127430003351 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_351
  have hV : (18560460520479399657124196974776393 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11190582883251 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_350 (Vfield_monotoneOn (show (11190582883251 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11190582883251 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_351 : (2329501739441743344420012084010093 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (1127430003351 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1127430003351 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (7419588474597 / 12500000000000 : ℝ) ≤ Real.sqrt (1127430003351 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1127430003351 / 3200000000000 : ℝ) ≤ (59356707796777 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (59356707796777 / 100000000000000 : ℝ) = (100000000000000 / 59356707796777 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7419588474597 / 12500000000000 : ℝ) = (312500000000 / 2473196158199 : ℝ) := by norm_num
  have hL1 : (6036460465701 / 20000000000000 : ℝ) ≤ Real.log (1 + (1127430003351 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1127430003351 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-102737069400221 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (59356707796777 / 216289375097091 : ℝ) ≤ (133918995915679 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (59356707796777 / 100000000000000 : ℝ) ≤ (133918995915679 / 250000000000000 : ℝ) := by
    have hw : (116289375097091 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (59356707796777 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (59356707796777 / 100000000000000 : ℝ) / (1 + (116289375097091 / 100000000000000 : ℝ)) = (59356707796777 / 216289375097091 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (103512034313218061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 59356707796777 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 59356707796777 : ℝ) = (59356707796777 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (312500000000 / 2473196158199 : ℝ) ≤ (125688646329699 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (103512034313218061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (59356707796777 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7419588474597 / 12500000000000 : ℝ)) ≤ (125688646329699 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_351 : ∀ t : ℝ, (1127430003351 / 3200000000000 : ℝ) < t → t ≤ (11358017183769 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-72971442148958156818049557 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11358017183769 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_352
  have hV : (2329501739441743344420012084010093 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1127430003351 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_351 (Vfield_monotoneOn (show (1127430003351 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1127430003351 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_352 : (18711312414175773487686662717781441 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (11358017183769 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11358017183769 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (59576676392089 / 100000000000000 : ℝ) ≤ Real.sqrt (11358017183769 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11358017183769 / 32000000000000 : ℝ) ≤ (5957667639209 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5957667639209 / 10000000000000 : ℝ) = (10000000000000 / 5957667639209 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (59576676392089 / 100000000000000 : ℝ) = (7500000000000 / 59576676392089 : ℝ) := by norm_num
  have hL1 : (30375572412943 / 100000000000000 : ℝ) ≤ Real.log (1 + (11358017183769 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11358017183769 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-102008847712669 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (29788338196045 / 108200902849371 : ℝ) ≤ (268650506336423 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5957667639209 / 10000000000000 : ℝ) ≤ (268650506336423 / 500000000000000 : ℝ) := by
    have hw : (58200902849371 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (5957667639209 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (5957667639209 / 10000000000000 : ℝ) / (1 + (58200902849371 / 50000000000000 : ℝ)) = (29788338196045 / 108200902849371 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (103349531412205061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 5957667639209 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 5957667639209 : ℝ) = (5957667639209 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 59576676392089 : ℝ) ≤ (12522942498037 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (103349531412205061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5957667639209 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (59576676392089 / 100000000000000 : ℝ)) ≤ (12522942498037 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_352 : ∀ t : ℝ, (11358017183769 / 32000000000000 : ℝ) < t → t ≤ (22799751517797 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-145466843381208520806308293 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (22799751517797 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_353
  have hV : (18711312414175773487686662717781441 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11358017183769 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_352 (Vfield_monotoneOn (show (11358017183769 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11358017183769 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_353 : (18748866842230049365752499962414753 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (22799751517797 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (22799751517797 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (59686356687737 / 100000000000000 : ℝ) ≤ Real.sqrt (22799751517797 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (22799751517797 / 64000000000000 : ℝ) ≤ (29843178343869 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (29843178343869 / 50000000000000 : ℝ) = (50000000000000 / 29843178343869 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (59686356687737 / 100000000000000 : ℝ) = (7500000000000 / 59686356687737 : ℝ) := by norm_num
  have hL1 : (15236033780217 / 50000000000000 : ℝ) ≤ Real.log (1 + (22799751517797 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((22799751517797 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-101646715913049 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (29843178343869 / 108228990148069 : ℝ) ≤ (269055053995793 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (29843178343869 / 50000000000000 : ℝ) ≤ (269055053995793 / 500000000000000 : ℝ) := by
    have hw : (58228990148069 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (29843178343869 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (29843178343869 / 50000000000000 : ℝ) / (1 + (58228990148069 / 50000000000000 : ℝ)) = (29843178343869 / 108228990148069 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (103268621880331061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 29843178343869 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 29843178343869 : ℝ) = (29843178343869 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 59686356687737 : ℝ) ≤ (1953151467099 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (103268621880331061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (29843178343869 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (59686356687737 / 100000000000000 : ℝ)) ≤ (1953151467099 / 15625000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_353 : ∀ t : ℝ, (22799751517797 / 64000000000000 : ℝ) < t → t ≤ (2860433583507 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-145006823752928046253978453 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2860433583507 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_354
  have hV : (18748866842230049365752499962414753 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (22799751517797 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_353 (Vfield_monotoneOn (show (22799751517797 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (22799751517797 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_354 : (4696589614797503532030067910148671 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (2860433583507 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2860433583507 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (14948958950759 / 25000000000000 : ℝ) ≤ Real.sqrt (2860433583507 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2860433583507 / 8000000000000 : ℝ) ≤ (59795835803037 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (59795835803037 / 100000000000000 : ℝ) = (100000000000000 / 59795835803037 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14948958950759 / 25000000000000 : ℝ) = (1875000000000 / 14948958950759 : ℝ) := by norm_num
  have hL1 : (15284234842273 / 50000000000000 : ℝ) ≤ Real.log (1 + (2860433583507 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2860433583507 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-101285890777409 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (59795835803037 / 216514127810252 : ℝ) ≤ (269458470338821 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (59795835803037 / 100000000000000 : ℝ) ≤ (269458470338821 / 500000000000000 : ℝ) := by
    have hw : (29128531952563 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (59795835803037 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (59795835803037 / 100000000000000 : ℝ) / (1 + (29128531952563 / 25000000000000 : ℝ)) = (59795835803037 / 216514127810252 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (103187938611725461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 59795835803037 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 59795835803037 : ℝ) = (59795835803037 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 14948958950759 : ℝ) ≤ (7798450045507 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (103187938611725461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (59795835803037 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14948958950759 / 25000000000000 : ℝ)) ≤ (7798450045507 / 62500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_354 : ∀ t : ℝ, (2860433583507 / 8000000000000 : ℝ) < t → t ≤ (4593437163663 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-72280091727161186349312799 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4593437163663 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_355
  have hV : (4696589614797503532030067910148671 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2860433583507 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_354 (Vfield_monotoneOn (show (2860433583507 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2860433583507 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_355 : (3764757512876405356230223859788493 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (4593437163663 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4593437163663 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (11981022968197 / 20000000000000 : ℝ) ≤ Real.sqrt (4593437163663 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4593437163663 / 12800000000000 : ℝ) ≤ (29952557420493 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (29952557420493 / 50000000000000 : ℝ) = (50000000000000 / 29952557420493 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (11981022968197 / 20000000000000 : ℝ) = (1500000000000 / 11981022968197 : ℝ) := by norm_num
  have hL1 : (30664778964459 / 100000000000000 : ℝ) ≤ Real.log (1 + (4593437163663 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4593437163663 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-100926362910087 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (29952557420493 / 108285124140109 : ℝ) ≤ (269860761605131 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (29952557420493 / 50000000000000 : ℝ) ≤ (269860761605131 / 500000000000000 : ℝ) := by
    have hw : (58285124140109 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (29952557420493 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (29952557420493 / 50000000000000 : ℝ) / (1 + (58285124140109 / 50000000000000 : ℝ)) = (29952557420493 / 108285124140109 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (103107480358463461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 29952557420493 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 29952557420493 : ℝ) = (29952557420493 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 11981022968197 : ℝ) ≤ (124549934306627 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (103107480358463461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (29952557420493 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (11981022968197 / 20000000000000 : ℝ)) ≤ (124549934306627 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_355 : ∀ t : ℝ, (4593437163663 / 12800000000000 : ℝ) < t → t ≤ (11525451484287 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-72062495949951731306253367 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11525451484287 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_356
  have hV : (3764757512876405356230223859788493 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4593437163663 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_355 (Vfield_monotoneOn (show (4593437163663 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4593437163663 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_356 : (9430577227386374213440919151514861 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (11525451484287 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11525451484287 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (30007097447269 / 50000000000000 : ℝ) ≤ Real.sqrt (11525451484287 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11525451484287 / 32000000000000 : ℝ) ≤ (60014194894539 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (60014194894539 / 100000000000000 : ℝ) = (100000000000000 / 60014194894539 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (30007097447269 / 50000000000000 : ℝ) = (3750000000000 / 30007097447269 : ℝ) := by norm_num
  have hL1 : (7690248894709 / 25000000000000 : ℝ) ≤ Real.log (1 + (11525451484287 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11525451484287 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-25142030754099 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (60014194894539 / 216626341745077 : ℝ) ≤ (270261933979391 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (60014194894539 / 100000000000000 : ℝ) ≤ (270261933979391 / 500000000000000 : ℝ) := by
    have hw : (116626341745077 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (60014194894539 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (60014194894539 / 100000000000000 : ℝ) / (1 + (116626341745077 / 100000000000000 : ℝ)) = (60014194894539 / 216626341745077 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (103027245883611461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 60014194894539 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 60014194894539 : ℝ) = (60014194894539 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 30007097447269 : ℝ) ≤ (15540735449443 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (103027245883611461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (60014194894539 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (30007097447269 / 50000000000000 : ℝ)) ≤ (15540735449443 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_356 : ∀ t : ℝ, (11525451484287 / 32000000000000 : ℝ) < t → t ≤ (23134620118833 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-14369978574398136518140989 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23134620118833 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_357
  have hV : (9430577227386374213440919151514861 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11525451484287 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_356 (Vfield_monotoneOn (show (11525451484287 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11525451484287 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_357 : (3779691884999304301086299114382843 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (23134620118833 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23134620118833 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (12024615409347 / 20000000000000 : ℝ) ≤ Real.sqrt (23134620118833 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23134620118833 / 64000000000000 : ℝ) ≤ (3757692315421 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3757692315421 / 6250000000000 : ℝ) = (6250000000000 / 3757692315421 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (12024615409347 / 20000000000000 : ℝ) = (500000000000 / 4008205136449 : ℝ) := by norm_num
  have hL1 : (15428559852913 / 50000000000000 : ℝ) ≤ Real.log (1 + (23134620118833 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23134620118833 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-25052790475297 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (30061538523368 / 108341204121889 : ℝ) ≤ (270661993592007 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3757692315421 / 6250000000000 : ℝ) ≤ (270661993592007 / 500000000000000 : ℝ) := by
    have hw : (58341204121889 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (3757692315421 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3757692315421 / 6250000000000 : ℝ) / (1 + (58341204121889 / 50000000000000 : ℝ)) = (30061538523368 / 108341204121889 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102947233961088261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 3757692315421 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 3757692315421 : ℝ) = (3757692315421 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4008205136449 : ℝ) ≤ (62051518849491 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102947233961088261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3757692315421 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (12024615409347 / 20000000000000 : ℝ)) ≤ (62051518849491 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_357 : ∀ t : ℝ, (23134620118833 / 64000000000000 : ℝ) < t → t ≤ (5804584317273 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-143283423011480037834075829 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5804584317273 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_358
  have hV : (3779691884999304301086299114382843 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23134620118833 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_357 (Vfield_monotoneOn (show (23134620118833 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23134620118833 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_358 : (757428110695186168218338176631577 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (5804584317273 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (5804584317273 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (2409270494833 / 4000000000000 : ℝ) ≤ Real.sqrt (5804584317273 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (5804584317273 / 16000000000000 : ℝ) ≤ (30115881185413 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (30115881185413 / 50000000000000 : ℝ) = (50000000000000 / 30115881185413 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2409270494833 / 4000000000000 : ℝ) = (300000000000 / 2409270494833 : ℝ) := by norm_num
  have hL1 : (30953151523063 / 100000000000000 : ℝ) ≤ Real.log (1 + (5804584317273 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((5804584317273 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-12481933808429 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (30115881185413 / 108369223907586 : ℝ) ≤ (135530473259893 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (30115881185413 / 50000000000000 : ℝ) ≤ (135530473259893 / 250000000000000 : ℝ) := by
    have hw : (29184611953793 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (30115881185413 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (30115881185413 / 50000000000000 : ℝ) / (1 + (29184611953793 / 25000000000000 : ℝ)) = (30115881185413 / 108369223907586 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102867443375532461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 30115881185413 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 30115881185413 : ℝ) = (30115881185413 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (300000000000 / 2409270494833 : ℝ) ≤ (7742586616081 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102867443375532461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (30115881185413 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2409270494833 / 4000000000000 : ℝ)) ≤ (7742586616081 / 62500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_358 : ∀ t : ℝ, (5804584317273 / 16000000000000 : ℝ) < t → t ≤ (46520391688443 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-143078265595792191534109729 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (46520391688443 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_359
  have hV : (757428110695186168218338176631577 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (5804584317273 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_358 (Vfield_monotoneOn (show (5804584317273 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (5804584317273 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_359 : (758172056754348394459661705989107 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (46520391688443 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (46520391688443 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (2411441262203 / 4000000000000 : ℝ) ≤ Real.sqrt (46520391688443 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (46520391688443 / 128000000000000 : ℝ) ≤ (15071507888769 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (15071507888769 / 25000000000000 : ℝ) = (25000000000000 / 15071507888769 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2411441262203 / 4000000000000 : ℝ) = (300000000000 / 2411441262203 : ℝ) := by norm_num
  have hL1 : (15500566435447 / 50000000000000 : ℝ) ≤ Real.log (1 + (46520391688443 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((46520391688443 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-99678098064763 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (379157431164 / 1363311053555 : ℝ) ≤ (2170080078891 / 8000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (15071507888769 / 25000000000000 : ℝ) ≤ (2170080078891 / 4000000000000 : ℝ) := by
    have hw : (23353291503049 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (15071507888769 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (15071507888769 / 25000000000000 : ℝ) / (1 + (23353291503049 / 20000000000000 : ℝ)) = (379157431164 / 1363311053555 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (102827630707214661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 15071507888769 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 15071507888769 : ℝ) = (15071507888769 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (300000000000 / 2411441262203 : ℝ) ≤ (15471375547669 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (102827630707214661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (15071507888769 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2411441262203 / 4000000000000 : ℝ)) ≤ (15471375547669 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_359 : ∀ t : ℝ, (46520391688443 / 128000000000000 : ℝ) < t → t ≤ (23302054419351 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-142874991116854739420066417 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23302054419351 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_360
  have hV : (758172056754348394459661705989107 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (46520391688443 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_359 (Vfield_monotoneOn (show (46520391688443 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (46520391688443 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
