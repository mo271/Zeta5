import Apery.Table2.U13
import Apery.Table2.U14

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_520 : (24447831360776223925512026251388471 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9287519810631 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9287519810631 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (76188581044959 / 100000000000000 : ℝ) ≤ Real.sqrt (9287519810631 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9287519810631 / 16000000000000 : ℝ) ≤ (476178631531 / 625000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (476178631531 / 625000000000 : ℝ) = (625000000000 / 476178631531 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (76188581044959 / 100000000000000 : ℝ) = (2500000000000 / 25396193681653 : ℝ) := by norm_num
  have hL1 : (45772226366973 / 100000000000000 : ℝ) ≤ Real.log (1 + (9287519810631 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9287519810631 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-26713670321877 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7618858104496 / 22571674463509 : ℝ) ≤ (325532365264507 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (476178631531 / 625000000000 : ℝ) ≤ (325532365264507 / 500000000000000 : ℝ) := by
    have hw : (12571674463509 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (476178631531 / 625000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (476178631531 / 625000000000 : ℝ) / (1 + (12571674463509 / 10000000000000 : ℝ)) = (7618858104496 / 22571674463509 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (91973159626588261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (625000000000 / 476178631531 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (625000000000 / 476178631531 : ℝ) = (476178631531 / 625000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 25396193681653 : ℝ) ≤ (98123809730503 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (91973159626588261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (476178631531 / 625000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (76188581044959 / 100000000000000 : ℝ)) ≤ (98123809730503 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_520 : ∀ t : ℝ, (9287519810631 / 16000000000000 : ℝ) < t → t ≤ (4683703346333 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-87796785989821869729277789 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4683703346333 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_521
  have hV : (24447831360776223925512026251388471 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9287519810631 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_520 (Vfield_monotoneOn (show (9287519810631 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9287519810631 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_521 : (24561380657295645053554787710815383 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4683703346333 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4683703346333 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (76515548635007 / 100000000000000 : ℝ) ≤ Real.sqrt (4683703346333 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4683703346333 / 8000000000000 : ℝ) ≤ (597777723711 / 781250000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (597777723711 / 781250000000 : ℝ) = (781250000000 / 597777723711 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (76515548635007 / 100000000000000 : ℝ) = (7500000000000 / 76515548635007 : ℝ) := by norm_num
  have hL1 : (46087642670107 / 100000000000000 : ℝ) ≤ Real.log (1 + (4683703346333 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4683703346333 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-410773836301 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (4250863813056 / 12550842589553 : ℝ) ≤ (326565135821633 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (597777723711 / 781250000000 : ℝ) ≤ (326565135821633 / 500000000000000 : ℝ) := by
    have hw : (62957583305977 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (597777723711 / 781250000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (597777723711 / 781250000000 : ℝ) / (1 + (62957583305977 / 50000000000000 : ℝ)) = (4250863813056 / 12550842589553 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (91766605515163061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (781250000000 / 597777723711 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (781250000000 / 597777723711 : ℝ) = (597777723711 / 781250000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 76515548635007 : ℝ) ≤ (48853587275793 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (91766605515163061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (597777723711 / 781250000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (76515548635007 / 100000000000000 : ℝ)) ≤ (48853587275793 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_521 : ∀ t : ℝ, (4683703346333 / 8000000000000 : ℝ) < t → t ≤ (9447293574701 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-17369437703034650572221581 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9447293574701 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_522
  have hV : (24561380657295645053554787710815383 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4683703346333 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_521 (Vfield_monotoneOn (show (4683703346333 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4683703346333 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_522 : (24674460665349303137891244193980243 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9447293574701 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9447293574701 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (76841124953947 / 100000000000000 : ℝ) ≤ Real.sqrt (9447293574701 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9447293574701 / 16000000000000 : ℝ) ≤ (19210281238487 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19210281238487 / 25000000000000 : ℝ) = (25000000000000 / 19210281238487 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (76841124953947 / 100000000000000 : ℝ) = (7500000000000 / 76841124953947 : ℝ) := by norm_num
  have hL1 : (90629037551 / 195312500000 : ℝ) ≤ Real.log (1 + (9447293574701 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9447293574701 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6467237114341 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (76841124953948 / 226113276399387 : ℝ) ≤ (81897569595329 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19210281238487 / 25000000000000 : ℝ) ≤ (81897569595329 / 125000000000000 : ℝ) := by
    have hw : (126113276399387 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (19210281238487 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (19210281238487 / 25000000000000 : ℝ) / (1 + (126113276399387 / 100000000000000 : ℝ)) = (76841124953948 / 226113276399387 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (91561577003226461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 19210281238487 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 19210281238487 : ℝ) = (19210281238487 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 76841124953947 : ℝ) ≤ (19459160371919 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (91561577003226461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19210281238487 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (76841124953947 / 100000000000000 : ℝ)) ≤ (19459160371919 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_522 : ∀ t : ℝ, (9447293574701 / 16000000000000 : ℝ) < t → t ≤ (297724389273 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-10739170770682235044047313 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (297724389273 / 500000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_523
  have hV : (24674460665349303137891244193980243 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9447293574701 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_522 (Vfield_monotoneOn (show (9447293574701 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9447293574701 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_523 : (1549192303865659394600468316944443 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (297724389273 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (297724389273 / 500000000000 : ℝ) := by norm_num
  have hs1 : (4822832975747 / 6250000000000 : ℝ) ≤ Real.sqrt (297724389273 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (297724389273 / 500000000000 : ℝ) ≤ (77165327611953 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (77165327611953 / 100000000000000 : ℝ) = (100000000000000 / 77165327611953 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4822832975747 / 6250000000000 : ℝ) = (468750000000 / 4822832975747 : ℝ) := by norm_num
  have hL1 : (46715506252041 / 100000000000000 : ℝ) ≤ Real.log (1 + (297724389273 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((297724389273 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2545187960387 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (2857975096739 / 8381891683938 : ℝ) ≤ (32860789603759 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (77165327611953 / 100000000000000 : ℝ) ≤ (32860789603759 / 50000000000000 : ℝ) := by
    have hw : (63155537733163 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (77165327611953 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (77165327611953 / 100000000000000 : ℝ) / (1 + (63155537733163 / 50000000000000 : ℝ)) = (2857975096739 / 8381891683938 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (91358053471971661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 77165327611953 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 77165327611953 : ℝ) = (77165327611953 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (468750000000 / 4822832975747 : ℝ) ≤ (96889581794971 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (91358053471971661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (77165327611953 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4822832975747 / 6250000000000 : ℝ)) ≤ (96889581794971 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_523 : ∀ t : ℝ, (297724389273 / 500000000000 : ℝ) < t → t ≤ (19123153518409 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-84809236103906965419105507 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19123153518409 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_524
  have hV : (1549192303865659394600468316944443 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (297724389273 / 500000000000 : ℝ) := by norm_num
    refine le_trans V_pt_523 (Vfield_monotoneOn (show (297724389273 / 500000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (297724389273 / 500000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_524 : (6208855921263417680544817066358239 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (19123153518409 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19123153518409 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (19326124602631 / 25000000000000 : ℝ) ≤ Real.sqrt (19123153518409 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19123153518409 / 32000000000000 : ℝ) ≤ (3092179936421 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3092179936421 / 4000000000000 : ℝ) = (4000000000000 / 3092179936421 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19326124602631 / 25000000000000 : ℝ) = (1875000000000 / 19326124602631 : ℝ) := by norm_num
  have hL1 : (23425079695583 / 50000000000000 : ℝ) ≤ Real.log (1 + (19123153518409 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19123153518409 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-25273371262009 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (77304498410525 / 226396145014406 : ℝ) ≤ (41130468990687 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3092179936421 / 4000000000000 : ℝ) ≤ (41130468990687 / 62500000000000 : ℝ) := by
    have hw : (63198072507203 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (3092179936421 / 4000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3092179936421 / 4000000000000 : ℝ) / (1 + (63198072507203 / 50000000000000 : ℝ)) = (77304498410525 / 226396145014406 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (91270882294390461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 3092179936421 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 3092179936421 : ℝ) = (3092179936421 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 19326124602631 : ℝ) ≤ (96716238778259 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (91270882294390461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3092179936421 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19326124602631 / 25000000000000 : ℝ)) ≤ (96716238778259 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_524 : ∀ t : ℝ, (19123153518409 / 32000000000000 : ℝ) < t → t ≤ (9595973061673 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-16824478104113073052550169 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9595973061673 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_525
  have hV : (6208855921263417680544817066358239 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19123153518409 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_524 (Vfield_monotoneOn (show (19123153518409 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19123153518409 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_525 : (6220921486267396964134642480934771 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (9595973061673 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9595973061673 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (19360854777659 / 25000000000000 : ℝ) ≤ Real.sqrt (9595973061673 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9595973061673 / 16000000000000 : ℝ) ≤ (77443419110637 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (77443419110637 / 100000000000000 : ℝ) = (100000000000000 / 77443419110637 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19360854777659 / 25000000000000 : ℝ) = (1875000000000 / 19360854777659 : ℝ) := by norm_num
  have hL1 : (46984631459403 / 100000000000000 : ℝ) ≤ Real.log (1 + (9595973061673 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9595973061673 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-25095497958191 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (77443419110637 / 226481157345850 : ℝ) ≤ (164739119750979 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (77443419110637 / 100000000000000 : ℝ) ≤ (164739119750979 / 250000000000000 : ℝ) := by
    have hw : (2529623146917 / 2000000000000 : ℝ) ≤ Real.sqrt (1 + (77443419110637 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (77443419110637 / 100000000000000 : ℝ) / (1 + (2529623146917 / 2000000000000 : ℝ)) = (77443419110637 / 226481157345850 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (91183984779098061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 77443419110637 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 77443419110637 : ℝ) = (77443419110637 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 19360854777659 : ℝ) ≤ (24135955706153 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (91183984779098061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (77443419110637 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19360854777659 / 25000000000000 : ℝ)) ≤ (24135955706153 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_525 : ∀ t : ℝ, (9595973061673 / 16000000000000 : ℝ) < t → t ≤ (19260738728283 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-41753284902744463823449913 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19260738728283 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_526
  have hV : (6220921486267396964134642480934771 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9595973061673 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_525 (Vfield_monotoneOn (show (9595973061673 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9595973061673 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_526 : (24931864061362580989950317800695203 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (19260738728283 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19260738728283 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (77582091055787 / 100000000000000 : ℝ) ≤ Real.sqrt (19260738728283 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19260738728283 / 32000000000000 : ℝ) ≤ (19395522763947 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19395522763947 / 25000000000000 : ℝ) = (25000000000000 / 19395522763947 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (77582091055787 / 100000000000000 : ℝ) = (7500000000000 / 77582091055787 : ℝ) := by norm_num
  have hL1 : (47118922943077 / 100000000000000 : ℝ) ≤ Real.log (1 + (19260738728283 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19260738728283 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2491825519017 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (273176376957 / 797768002028 : ℝ) ≤ (329911366638311 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19395522763947 / 25000000000000 : ℝ) ≤ (329911366638311 / 500000000000000 : ℝ) := by
    have hw : (7910382035997 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (19395522763947 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (19395522763947 / 25000000000000 : ℝ) / (1 + (7910382035997 / 6250000000000 : ℝ)) = (273176376957 / 797768002028 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (91097359351827461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 19395522763947 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 19395522763947 : ℝ) = (19395522763947 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 77582091055787 : ℝ) ≤ (2409308142497 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (91097359351827461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19395522763947 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (77582091055787 / 100000000000000 : ℝ)) ≤ (2409308142497 / 25000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_526 : ∀ t : ℝ, (19260738728283 / 32000000000000 : ℝ) < t → t ≤ (38590270061503 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-83213947086615649056968529 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (38590270061503 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_527
  have hV : (24931864061362580989950317800695203 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19260738728283 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_526 (Vfield_monotoneOn (show (19260738728283 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19260738728283 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_527 : (12477960847878845724803227509412483 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (38590270061503 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (38590270061503 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (38825667080907 / 50000000000000 : ℝ) ≤ Real.sqrt (38590270061503 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (38590270061503 / 64000000000000 : ℝ) ≤ (15530266832363 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (15530266832363 / 20000000000000 : ℝ) = (20000000000000 / 15530266832363 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (38825667080907 / 50000000000000 : ℝ) = (1250000000000 / 12941889026969 : ℝ) := by norm_num
  have hL1 : (5898250139643 / 12500000000000 : ℝ) ≤ Real.log (1 + (38590270061503 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((38590270061503 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6207467215799 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (77651334161815 / 226608568813922 : ℝ) ≤ (165063711241167 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (15530266832363 / 20000000000000 : ℝ) ≤ (165063711241167 / 250000000000000 : ℝ) := by
    have hw : (63304284406961 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (15530266832363 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (15530266832363 / 20000000000000 : ℝ) / (1 + (63304284406961 / 50000000000000 : ℝ)) = (77651334161815 / 226608568813922 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (91054148183022861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 15530266832363 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 15530266832363 : ℝ) = (15530266832363 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 12941889026969 : ℝ) ≤ (12035864894141 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (91054148183022861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (15530266832363 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (38825667080907 / 50000000000000 : ℝ)) ≤ (12035864894141 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_527 : ∀ t : ℝ, (38590270061503 / 64000000000000 : ℝ) < t → t ≤ (966476566661 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-82928800459040657138797021 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (966476566661 / 1600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_528
  have hV : (12477960847878845724803227509412483 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (38590270061503 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_527 (Vfield_monotoneOn (show (38590270061503 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (38590270061503 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_528 : (6244989612492930104549330828977837 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (966476566661 / 1600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (966476566661 / 1600000000000 : ℝ) := by norm_num
  have hs1 : (19430128894373 / 25000000000000 : ℝ) ≤ Real.sqrt (966476566661 / 1600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (966476566661 / 1600000000000 : ℝ) ≤ (77720515577493 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (77720515577493 / 100000000000000 : ℝ) = (100000000000000 / 77720515577493 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19430128894373 / 25000000000000 : ℝ) = (1875000000000 / 19430128894373 : ℝ) := by norm_num
  have hL1 : (47253034326557 / 100000000000000 : ℝ) ≤ Real.log (1 + (966476566661 / 1600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((966476566661 / 1600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24741638503411 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (135637898041 / 395551502303 : ℝ) ≤ (8258578528421 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (77720515577493 / 100000000000000 : ℝ) ≤ (8258578528421 / 12500000000000 : ℝ) := by
    have hw : (126651010819619 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (77720515577493 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (77720515577493 / 100000000000000 : ℝ) / (1 + (126651010819619 / 100000000000000 : ℝ)) = (135637898041 / 395551502303 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (91011004452121661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 77720515577493 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 77720515577493 : ℝ) = (77720515577493 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 19430128894373 : ℝ) ≤ (96201739271939 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (91011004452121661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (77720515577493 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19430128894373 / 25000000000000 : ℝ)) ≤ (96201739271939 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_528 : ∀ t : ℝ, (966476566661 / 1600000000000 : ℝ) < t → t ≤ (38727855271377 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-41324939541763344610947369 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (38727855271377 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_529
  have hV : (6244989612492930104549330828977837 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (966476566661 / 1600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_528 (Vfield_monotoneOn (show (966476566661 / 1600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (966476566661 / 1600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_529 : (2500397437547990956284893738328829 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (38727855271377 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (38727855271377 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (7778963546741 / 10000000000000 : ℝ) ≤ Real.sqrt (38727855271377 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (38727855271377 / 64000000000000 : ℝ) ≤ (77789635467411 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (77789635467411 / 100000000000000 : ℝ) = (100000000000000 / 77789635467411 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7778963546741 / 10000000000000 : ℝ) = (750000000000 / 7778963546741 : ℝ) := by norm_num
  have hL1 : (23660011315779 / 50000000000000 : ℝ) ≤ Real.log (1 + (38727855271377 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((38727855271377 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24653563561343 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (25929878489137 / 75564479535781 : ℝ) ≤ (330558523566457 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (77789635467411 / 100000000000000 : ℝ) ≤ (330558523566457 / 500000000000000 : ℝ) := by
    have hw : (126693438607343 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (77789635467411 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (77789635467411 / 100000000000000 : ℝ) / (1 + (126693438607343 / 100000000000000 : ℝ)) = (25929878489137 / 75564479535781 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90967927966198261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 77789635467411 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 77789635467411 : ℝ) = (77789635467411 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 7778963546741 : ℝ) ≤ (24029196263869 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90967927966198261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (77789635467411 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7778963546741 / 10000000000000 : ℝ)) ≤ (24029196263869 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_529 : ∀ t : ℝ, (38727855271377 / 64000000000000 : ℝ) < t → t ≤ (19398323938157 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5148516894530447304575581 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19398323938157 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_530
  have hV : (2500397437547990956284893738328829 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (38727855271377 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_529 (Vfield_monotoneOn (show (38727855271377 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (38727855271377 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_530 : (2502796952354950455717129121303567 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (19398323938157 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19398323938157 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (7785869399543 / 10000000000000 : ℝ) ≤ Real.sqrt (19398323938157 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19398323938157 / 32000000000000 : ℝ) ≤ (77858693995431 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (77858693995431 / 100000000000000 : ℝ) = (100000000000000 / 77858693995431 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7785869399543 / 10000000000000 : ℝ) = (750000000000 / 7785869399543 : ℝ) := by norm_num
  have hL1 : (47386966092267 / 100000000000000 : ℝ) ≤ Real.log (1 + (19398323938157 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19398323938157 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-12282821745209 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (25952897998477 / 75578617397125 : ℝ) ≤ (330773570731609 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (77858693995431 / 100000000000000 : ℝ) ≤ (330773570731609 / 500000000000000 : ℝ) := by
    have hw : (1013886817531 / 800000000000 : ℝ) ≤ Real.sqrt (1 + (77858693995431 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (77858693995431 / 100000000000000 : ℝ) / (1 + (1013886817531 / 800000000000 : ℝ)) = (25952897998477 / 75578617397125 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90924918533167861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 77858693995431 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 77858693995431 : ℝ) = (77858693995431 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 7785869399543 : ℝ) ≤ (96032055509073 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90924918533167861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (77858693995431 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7785869399543 / 10000000000000 : ℝ)) ≤ (96032055509073 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_530 : ∀ t : ℝ, (19398323938157 / 32000000000000 : ℝ) < t → t ≤ (38865440481251 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-41053641759689365875274013 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (38865440481251 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_531
  have hV : (2502796952354950455717129121303567 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19398323938157 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_530 (Vfield_monotoneOn (show (19398323938157 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19398323938157 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_531 : (5010388789047715154083431478881553 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (38865440481251 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (38865440481251 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (15585538264937 / 20000000000000 : ℝ) ≤ Real.sqrt (38865440481251 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (38865440481251 / 64000000000000 : ℝ) ≤ (38963845662343 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (38963845662343 / 50000000000000 : ℝ) = (50000000000000 / 38963845662343 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (15585538264937 / 20000000000000 : ℝ) = (1500000000000 / 15585538264937 : ℝ) := by norm_num
  have hL1 : (9490772953737 / 20000000000000 : ℝ) ≤ Real.log (1 + (38865440481251 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((38865440481251 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-48955755493881 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (5566263666049 / 16198446541855 : ℝ) ≤ (165494141794263 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (38963845662343 / 50000000000000 : ℝ) ≤ (165494141794263 / 250000000000000 : ℝ) := by
    have hw : (12677825158597 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (38963845662343 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (38963845662343 / 50000000000000 : ℝ) / (1 + (12677825158597 / 10000000000000 : ℝ)) = (5566263666049 / 16198446541855 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90881975961784461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 38963845662343 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 38963845662343 : ℝ) = (38963845662343 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 15585538264937 : ℝ) ≤ (95947549644197 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90881975961784461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (38963845662343 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (15585538264937 / 20000000000000 : ℝ)) ≤ (95947549644197 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_531 : ∀ t : ℝ, (38865440481251 / 64000000000000 : ℝ) < t → t ≤ (9733558271547 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5115148795770535164743257 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9733558271547 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_532
  have hV : (5010388789047715154083431478881553 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (38865440481251 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_531 (Vfield_monotoneOn (show (38865440481251 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (38865440481251 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_532 : (25075897691399257301140513405090941 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9733558271547 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9733558271547 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (77996627617589 / 100000000000000 : ℝ) ≤ Real.sqrt (9733558271547 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9733558271547 / 16000000000000 : ℝ) ≤ (7799662761759 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7799662761759 / 10000000000000 : ℝ) = (10000000000000 / 7799662761759 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (77996627617589 / 100000000000000 : ℝ) = (7500000000000 / 77996627617589 : ℝ) := by norm_num
  have hL1 : (11880179680173 / 25000000000000 : ℝ) ≤ Real.log (1 + (9733558271547 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9733558271547 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24390265790073 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (77996627617590 / 226820636805359 : ℝ) ≤ (331202663089283 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7799662761759 / 10000000000000 : ℝ) ≤ (331202663089283 / 500000000000000 : ℝ) := by
    have hw : (126820636805359 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7799662761759 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7799662761759 / 10000000000000 : ℝ) / (1 + (126820636805359 / 100000000000000 : ℝ)) = (77996627617590 / 226820636805359 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90839100061633061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 7799662761759 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 7799662761759 : ℝ) = (7799662761759 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 77996627617589 : ℝ) ≤ (95863266478389 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90839100061633061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7799662761759 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (77996627617589 / 100000000000000 : ℝ)) ≤ (95863266478389 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_532 : ∀ t : ℝ, (9733558271547 / 16000000000000 : ℝ) < t → t ≤ (312024205529 / 512000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-3263245314857354172585929 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (312024205529 / 512000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_533
  have hV : (25075897691399257301140513405090941 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9733558271547 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_532 (Vfield_monotoneOn (show (9733558271547 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9733558271547 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_533 : (25099830812677406653810384367603653 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (312024205529 / 512000000000 : ℝ) := by
  have hp : (0 : ℝ) < (312024205529 / 512000000000 : ℝ) := by norm_num
  have hs1 : (78065503035837 / 100000000000000 : ℝ) ≤ Real.sqrt (312024205529 / 512000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (312024205529 / 512000000000 : ℝ) ≤ (39032751517919 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39032751517919 / 50000000000000 : ℝ) = (50000000000000 / 39032751517919 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (78065503035837 / 100000000000000 : ℝ) = (2500000000000 / 26021834345279 : ℝ) := by norm_num
  have hL1 : (47587528008049 / 100000000000000 : ℝ) ≤ Real.log (1 + (312024205529 / 512000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((312024205529 / 512000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3037850885227 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (39032751517919 / 113431503931876 : ℝ) ≤ (33141671018181 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39032751517919 / 50000000000000 : ℝ) ≤ (33141671018181 / 50000000000000 : ℝ) := by
    have hw : (15857875982969 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (39032751517919 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (39032751517919 / 50000000000000 : ℝ) / (1 + (15857875982969 / 12500000000000 : ℝ)) = (39032751517919 / 113431503931876 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90796290643127661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 39032751517919 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 39032751517919 : ℝ) = (39032751517919 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 26021834345279 : ℝ) ≤ (47889602517611 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90796290643127661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39032751517919 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (78065503035837 / 100000000000000 : ℝ)) ≤ (47889602517611 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_533 : ∀ t : ℝ, (312024205529 / 512000000000 : ℝ) < t → t ≤ (19535909148031 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-20330797730967022193306053 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19535909148031 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_534
  have hV : (25099830812677406653810384367603653 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (312024205529 / 512000000000 : ℝ) := by norm_num
    refine le_trans V_pt_533 (Vfield_monotoneOn (show (312024205529 / 512000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (312024205529 / 512000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_534 : (6280935839878578693548757890249207 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (19535909148031 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19535909148031 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (19533579435103 / 25000000000000 : ℝ) ≤ Real.sqrt (19535909148031 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19535909148031 / 32000000000000 : ℝ) ≤ (78134317740413 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (78134317740413 / 100000000000000 : ℝ) = (100000000000000 / 78134317740413 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19533579435103 / 25000000000000 : ℝ) = (1875000000000 / 19533579435103 : ℝ) := by norm_num
  have hL1 : (11913573172599 / 25000000000000 : ℝ) ≤ Real.log (1 + (19535909148031 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19535909148031 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-48431002173977 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (78134317740413 / 226905364775330 : ℝ) ≤ (165815212904967 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (78134317740413 / 100000000000000 : ℝ) ≤ (165815212904967 / 250000000000000 : ℝ) := by
    have hw : (12690536477533 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (78134317740413 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (78134317740413 / 100000000000000 : ℝ) / (1 + (12690536477533 / 10000000000000 : ℝ)) = (78134317740413 / 226905364775330 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90753547517502861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 78134317740413 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 78134317740413 : ℝ) = (78134317740413 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 19533579435103 : ℝ) ≤ (95695364344253 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90753547517502861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (78134317740413 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19533579435103 / 25000000000000 : ℝ)) ≤ (95695364344253 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_534 : ∀ t : ℝ, (19535909148031 / 32000000000000 : ℝ) < t → t ≤ (39140610900999 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-40534133126765657476790771 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (39140610900999 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_535
  have hV : (6280935839878578693548757890249207 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19535909148031 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_534 (Vfield_monotoneOn (show (19535909148031 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19535909148031 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_535 : (25147635382148158688870298469396941 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (39140610900999 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (39140610900999 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (78203071891589 / 100000000000000 : ℝ) ≤ Real.sqrt (39140610900999 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (39140610900999 / 64000000000000 : ℝ) ≤ (7820307189159 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7820307189159 / 10000000000000 : ℝ) = (10000000000000 / 7820307189159 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (78203071891589 / 100000000000000 : ℝ) = (7500000000000 / 78203071891589 : ℝ) := by norm_num
  have hL1 : (23860506413627 / 50000000000000 : ℝ) ≤ Real.log (1 + (39140610900999 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((39140610900999 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3016043409151 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (26067690630530 / 75649235851419 : ℝ) ≤ (165921905456693 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7820307189159 / 10000000000000 : ℝ) ≤ (165921905456693 / 250000000000000 : ℝ) := by
    have hw : (126947707554257 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7820307189159 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7820307189159 / 10000000000000 : ℝ) / (1 + (126947707554257 / 100000000000000 : ℝ)) = (26067690630530 / 75649235851419 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90710870496812461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 7820307189159 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 7820307189159 : ℝ) = (7820307189159 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 78203071891589 : ℝ) ≤ (47805871720487 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90710870496812461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7820307189159 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (78203071891589 / 100000000000000 : ℝ)) ≤ (47805871720487 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_535 : ∀ t : ℝ, (39140610900999 / 64000000000000 : ℝ) < t → t ≤ (2450587719121 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5051007296158914295108213 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2450587719121 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_536
  have hV : (25147635382148158688870298469396941 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (39140610900999 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_535 (Vfield_monotoneOn (show (39140610900999 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (39140610900999 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_536 : (25171506930614607097764889597749091 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2450587719121 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2450587719121 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (78271765648939 / 100000000000000 : ℝ) ≤ Real.sqrt (2450587719121 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2450587719121 / 4000000000000 : ℝ) ≤ (3913588282447 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3913588282447 / 5000000000000 : ℝ) = (5000000000000 / 3913588282447 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (78271765648939 / 100000000000000 : ℝ) = (7500000000000 / 78271765648939 : ℝ) := by norm_num
  have hL1 : (5973461059753 / 12500000000000 : ℝ) ≤ Real.log (1 + (2450587719121 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2450587719121 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24041345110871 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (78271765648940 / 226990036214667 : ℝ) ≤ (332056866427843 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3913588282447 / 5000000000000 : ℝ) ≤ (332056866427843 / 500000000000000 : ℝ) := by
    have hw : (126990036214667 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (3913588282447 / 5000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3913588282447 / 5000000000000 : ℝ) / (1 + (126990036214667 / 100000000000000 : ℝ)) = (78271765648940 / 226990036214667 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90668259393921061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 3913588282447 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 3913588282447 : ℝ) = (3913588282447 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 78271765648939 : ℝ) ≤ (95528341366767 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90668259393921061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3913588282447 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (78271765648939 / 100000000000000 : ℝ)) ≤ (95528341366767 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_536 : ∀ t : ℝ, (2450587719121 / 4000000000000 : ℝ) < t → t ≤ (39278196110873 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-40283268378529490168815139 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (39278196110873 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_537
  have hV : (25171506930614607097764889597749091 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2450587719121 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_536 (Vfield_monotoneOn (show (2450587719121 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2450587719121 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_537 : (25195358054748306124290866270360077 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (39278196110873 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (39278196110873 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (78340399171333 / 100000000000000 : ℝ) ≤ Real.sqrt (39278196110873 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (39278196110873 / 64000000000000 : ℝ) ≤ (39170199585667 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39170199585667 / 50000000000000 : ℝ) = (50000000000000 / 39170199585667 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (78340399171333 / 100000000000000 : ℝ) = (7500000000000 / 78340399171333 : ℝ) := by norm_num
  have hL1 : (47854319701991 / 100000000000000 : ℝ) ≤ Real.log (1 + (39278196110873 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((39278196110873 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-11977247036567 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (78340399171334 / 227032350770675 : ℝ) ≤ (66453918656987 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39170199585667 / 50000000000000 : ℝ) ≤ (66453918656987 / 100000000000000 : ℝ) := by
    have hw : (5081294030827 / 4000000000000 : ℝ) ≤ Real.sqrt (1 + (39170199585667 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (39170199585667 / 50000000000000 : ℝ) / (1 + (5081294030827 / 4000000000000 : ℝ)) = (78340399171334 / 227032350770675 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90625714022502661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 39170199585667 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 39170199585667 : ℝ) = (39170199585667 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 78340399171333 : ℝ) ≤ (47722578584429 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90625714022502661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39170199585667 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (78340399171333 / 100000000000000 : ℝ)) ≤ (47722578584429 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_537 : ∀ t : ℝ, (39278196110873 / 64000000000000 : ℝ) < t → t ≤ (3934698871581 / 6400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-80319349790672479080732497 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (3934698871581 / 6400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_538
  have hV : (25195358054748306124290866270360077 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (39278196110873 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_537 (Vfield_monotoneOn (show (39278196110873 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (39278196110873 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_538 : (6304797201046047103665488359053253 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (3934698871581 / 6400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (3934698871581 / 6400000000000 : ℝ) := by norm_num
  have hs1 : (19602243154237 / 25000000000000 : ℝ) ≤ Real.sqrt (3934698871581 / 6400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (3934698871581 / 6400000000000 : ℝ) ≤ (78408972616949 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (78408972616949 / 100000000000000 : ℝ) = (100000000000000 / 78408972616949 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (19602243154237 / 25000000000000 : ℝ) = (1875000000000 / 19602243154237 : ℝ) := by norm_num
  have hL1 : (47920906558319 / 100000000000000 : ℝ) ≤ Real.log (1 + (3934698871581 / 6400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((3934698871581 / 6400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-47735587271787 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (78408972616949 / 227074651236371 : ℝ) ≤ (166240996206143 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (78408972616949 / 100000000000000 : ℝ) ≤ (166240996206143 / 250000000000000 : ℝ) := by
    have hw : (127074651236371 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (78408972616949 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (78408972616949 / 100000000000000 : ℝ) / (1 + (127074651236371 / 100000000000000 : ℝ)) = (78408972616949 / 227074651236371 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90583234197032461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 78408972616949 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 78408972616949 : ℝ) = (78408972616949 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 19602243154237 : ℝ) ≤ (23840547475067 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90583234197032461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (78408972616949 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (19602243154237 / 25000000000000 : ℝ)) ≤ (23840547475067 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_538 : ∀ t : ℝ, (3934698871581 / 6400000000000 : ℝ) < t → t ≤ (39415781320747 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-625581272300498507741657 / 781250000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (39415781320747 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_539
  have hV : (6304797201046047103665488359053253 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (3934698871581 / 6400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_538 (Vfield_monotoneOn (show (3934698871581 / 6400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (3934698871581 / 6400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_539 : (25242999228357281745785207995167323 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (39415781320747 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (39415781320747 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (78477486143267 / 100000000000000 : ℝ) ≤ Real.sqrt (39415781320747 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (39415781320747 / 64000000000000 : ℝ) ≤ (19619371535817 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19619371535817 / 25000000000000 : ℝ) = (25000000000000 / 19619371535817 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (78477486143267 / 100000000000000 : ℝ) = (7500000000000 / 78477486143267 : ℝ) := by norm_num
  have hL1 : (9597489821211 / 20000000000000 : ℝ) ≤ Real.log (1 + (39415781320747 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((39415781320747 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2972655409721 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (19619371535817 / 56779234406455 : ℝ) ≤ (332694064733517 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19619371535817 / 25000000000000 : ℝ) ≤ (332694064733517 / 500000000000000 : ℝ) := by
    have hw : (6355846881291 / 5000000000000 : ℝ) ≤ Real.sqrt (1 + (19619371535817 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (19619371535817 / 25000000000000 : ℝ) / (1 + (6355846881291 / 5000000000000 : ℝ)) = (19619371535817 / 56779234406455 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90540819732786261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 19619371535817 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 19619371535817 : ℝ) = (19619371535817 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 78477486143267 : ℝ) ≤ (744370614217 / 7812500000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90540819732786261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19619371535817 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (78477486143267 / 100000000000000 : ℝ)) ≤ (744370614217 / 7812500000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_539 : ∀ t : ℝ, (39415781320747 / 64000000000000 : ℝ) < t → t ≤ (9871143481421 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-4989472639413863690040911 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9871143481421 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_540
  have hV : (25242999228357281745785207995167323 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (39415781320747 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_539 (Vfield_monotoneOn (show (39415781320747 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (39415781320747 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_540 : (25266789376506020372090089948216441 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9871143481421 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9871143481421 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (78545939907089 / 100000000000000 : ℝ) ≤ Real.sqrt (9871143481421 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9871143481421 / 16000000000000 : ℝ) ≤ (7854593990709 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7854593990709 / 10000000000000 : ℝ) = (10000000000000 / 7854593990709 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (78545939907089 / 100000000000000 : ℝ) = (7500000000000 / 78545939907089 : ℝ) := by norm_num
  have hL1 : (48053947404127 / 100000000000000 : ℝ) ≤ Real.log (1 + (9871143481421 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9871143481421 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-296185531001 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (78545939907090 / 227159209953067 : ℝ) ≤ (83226452792073 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7854593990709 / 10000000000000 : ℝ) ≤ (83226452792073 / 125000000000000 : ℝ) := by
    have hw : (127159209953067 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7854593990709 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7854593990709 / 10000000000000 : ℝ) / (1 + (127159209953067 / 100000000000000 : ℝ)) = (78545939907090 / 227159209953067 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90498470445831261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 7854593990709 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 7854593990709 : ℝ) = (7854593990709 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 78545939907089 : ℝ) ≤ (95196902391861 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90498470445831261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7854593990709 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (78545939907089 / 100000000000000 : ℝ)) ≤ (95196902391861 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_540 : ∀ t : ℝ, (9871143481421 / 16000000000000 : ℝ) < t → t ≤ (39553366530621 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-318362840603563817784837 / 400000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (39553366530621 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_541
  have hV : (25266789376506020372090089948216441 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9871143481421 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_540 (Vfield_monotoneOn (show (9871143481421 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9871143481421 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_541 : (2529055929767176570776961192767357 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (39553366530621 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (39553366530621 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (7861433406453 / 10000000000000 : ℝ) ≤ Real.sqrt (39553366530621 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (39553366530621 / 64000000000000 : ℝ) ≤ (78614334064531 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (78614334064531 / 100000000000000 : ℝ) = (100000000000000 / 78614334064531 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7861433406453 / 10000000000000 : ℝ) = (250000000000 / 2620477802151 : ℝ) := by norm_num
  have hL1 : (48120401511347 / 100000000000000 : ℝ) ≤ Real.log (1 + (39553366530621 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((39553366530621 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-47217181453669 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (78614334064531 / 227201468232130 : ℝ) ≤ (83279308158083 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (78614334064531 / 100000000000000 : ℝ) ≤ (83279308158083 / 125000000000000 : ℝ) := by
    have hw : (12720146823213 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (78614334064531 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (78614334064531 / 100000000000000 : ℝ) / (1 + (12720146823213 / 10000000000000 : ℝ)) = (78614334064531 / 227201468232130 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90456186153023261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 78614334064531 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 78614334064531 : ℝ) = (78614334064531 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (250000000000 / 2620477802151 : ℝ) ≤ (95114580286671 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90456186153023261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (78614334064531 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7861433406453 / 10000000000000 : ℝ)) ≤ (95114580286671 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_541 : ∀ t : ℝ, (39553366530621 / 64000000000000 : ℝ) < t → t ≤ (19811079567779 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-3967587109092745401717291 / 5000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19811079567779 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_542
  have hV : (2529055929767176570776961192767357 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (39553366530621 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_541 (Vfield_monotoneOn (show (39553366530621 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (39553366530621 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_542 : (1012572361627989484769851806181729 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (19811079567779 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19811079567779 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (3147306750841 / 4000000000000 : ℝ) ≤ Real.sqrt (19811079567779 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19811079567779 / 32000000000000 : ℝ) ≤ (39341334385513 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39341334385513 / 50000000000000 : ℝ) = (50000000000000 / 39341334385513 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3147306750841 / 4000000000000 : ℝ) = (300000000000 / 3147306750841 : ℝ) := by norm_num
  have hL1 : (48186811486409 / 100000000000000 : ℝ) ≤ Real.log (1 + (19811079567779 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19811079567779 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-23522487504703 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (39341334385513 / 113621856238503 : ℝ) ≤ (13333133201497 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39341334385513 / 50000000000000 : ℝ) ≤ (13333133201497 / 20000000000000 : ℝ) := by
    have hw : (63621856238503 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (39341334385513 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (39341334385513 / 50000000000000 : ℝ) / (1 + (63621856238503 / 50000000000000 : ℝ)) = (39341334385513 / 113621856238503 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90413966672004661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 39341334385513 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 39341334385513 : ℝ) = (39341334385513 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (300000000000 / 3147306750841 : ℝ) ≤ (95032471379971 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90413966672004661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39341334385513 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3147306750841 / 4000000000000 : ℝ)) ≤ (95032471379971 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_542 : ∀ t : ℝ, (19811079567779 / 32000000000000 : ℝ) < t → t ≤ (7938190348099 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-79114565139079397053586331 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7938190348099 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_543
  have hV : (1012572361627989484769851806181729 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19811079567779 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_542 (Vfield_monotoneOn (show (19811079567779 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19811079567779 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_543 : (12669019327120883818048304342289461 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (7938190348099 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7938190348099 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (39375472090669 / 50000000000000 : ℝ) ≤ Real.sqrt (7938190348099 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7938190348099 / 12800000000000 : ℝ) ≤ (78750944181339 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (78750944181339 / 100000000000000 : ℝ) = (100000000000000 / 78750944181339 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (39375472090669 / 50000000000000 : ℝ) = (3750000000000 / 39375472090669 : ℝ) := by norm_num
  have hL1 : (12063294346973 / 25000000000000 : ℝ) ≤ Real.log (1 + (7938190348099 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7938190348099 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46873064606009 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (26250314727113 / 75761980900556 : ℝ) ≤ (166769552145739 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (78750944181339 / 100000000000000 : ℝ) ≤ (166769552145739 / 250000000000000 : ℝ) := by
    have hw : (31821485675417 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (78750944181339 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (78750944181339 / 100000000000000 : ℝ) / (1 + (31821485675417 / 25000000000000 : ℝ)) = (26250314727113 / 75761980900556 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90371811821194061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 78750944181339 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 78750944181339 : ℝ) = (78750944181339 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 39375472090669 : ℝ) ≤ (949505747531 / 10000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90371811821194061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (78750944181339 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (39375472090669 / 50000000000000 : ℝ)) ≤ (949505747531 / 10000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_543 : ∀ t : ℝ, (7938190348099 / 12800000000000 : ℝ) < t → t ≤ (4969968043179 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9859886925606904464648749 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4969968043179 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_544
  have hV : (12669019327120883818048304342289461 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7938190348099 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_543 (Vfield_monotoneOn (show (7938190348099 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7938190348099 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_544 : (25361748186755522788597967832697409 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4969968043179 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4969968043179 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (78819160449561 / 100000000000000 : ℝ) ≤ Real.sqrt (4969968043179 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4969968043179 / 8000000000000 : ℝ) ≤ (39409580224781 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39409580224781 / 50000000000000 : ℝ) = (50000000000000 / 39409580224781 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (78819160449561 / 100000000000000 : ℝ) = (2500000000000 / 26273053483187 : ℝ) := by norm_num
  have hL1 : (9663899854851 / 20000000000000 : ℝ) ≤ Real.log (1 + (4969968043179 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4969968043179 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-373611593819 / 800000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (39409580224781 / 113664079460033 : ℝ) ≤ (166874778149257 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39409580224781 / 50000000000000 : ℝ) ≤ (166874778149257 / 250000000000000 : ℝ) := by
    have hw : (63664079460033 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (39409580224781 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (39409580224781 / 50000000000000 : ℝ) / (1 + (63664079460033 / 50000000000000 : ℝ)) = (39409580224781 / 113664079460033 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90329721419786861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 39409580224781 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 39409580224781 : ℝ) = (39409580224781 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 26273053483187 : ℝ) ≤ (94868889492933 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90329721419786861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39409580224781 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (78819160449561 / 100000000000000 : ℝ)) ≤ (94868889492933 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_544 : ∀ t : ℝ, (4969968043179 / 8000000000000 : ℝ) < t → t ≤ (39828536950369 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9830657194739752442729269 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (39828536950369 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_545
  have hV : (25361748186755522788597967832697409 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4969968043179 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_544 (Vfield_monotoneOn (show (4969968043179 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4969968043179 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_545 : (158658985540666652036347220930583 / 31250000000000000000000000000000 : ℝ) ≤ Vfield (39828536950369 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (39828536950369 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (493045735807 / 625000000000 : ℝ) ≤ Real.sqrt (39828536950369 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (39828536950369 / 64000000000000 : ℝ) ≤ (78887317729121 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (78887317729121 / 100000000000000 : ℝ) = (100000000000000 / 78887317729121 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (493045735807 / 625000000000 : ℝ) = (46875000000 / 493045735807 : ℝ) := by norm_num
  have hL1 : (48385777203843 / 100000000000000 : ℝ) ≤ Real.log (1 + (39828536950369 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((39828536950369 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46530127862621 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (78887317729121 / 227370361146128 : ℝ) ≤ (333959686958707 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (78887317729121 / 100000000000000 : ℝ) ≤ (333959686958707 / 500000000000000 : ℝ) := by
    have hw : (7960647571633 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (78887317729121 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (78887317729121 / 100000000000000 : ℝ) / (1 + (7960647571633 / 6250000000000 : ℝ)) = (78887317729121 / 227370361146128 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90287695287748261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 78887317729121 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 78887317729121 : ℝ) = (78887317729121 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (46875000000 / 493045735807 : ℝ) ≤ (9478741469183 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90287695287748261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (78887317729121 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (493045735807 / 625000000000 : ℝ)) ≤ (9478741469183 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_545 : ∀ t : ℝ, (39828536950369 / 64000000000000 : ℝ) < t → t ≤ (19948664777653 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-39206491623567980924956067 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19948664777653 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_546
  have hV : (158658985540666652036347220930583 / 31250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (39828536950369 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_545 (Vfield_monotoneOn (show (39828536950369 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (39828536950369 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_546 : (25409107201568864819141668490410513 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (19948664777653 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19948664777653 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (78955416172777 / 100000000000000 : ℝ) ≤ Real.sqrt (19948664777653 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19948664777653 / 32000000000000 : ℝ) ≤ (39477708086389 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39477708086389 / 50000000000000 : ℝ) = (50000000000000 / 39477708086389 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (78955416172777 / 100000000000000 : ℝ) = (7500000000000 / 78955416172777 : ℝ) := by norm_num
  have hL1 : (9690402246977 / 20000000000000 : ℝ) ≤ Real.log (1 + (19948664777653 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19948664777653 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46359099506053 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (78955416172778 / 227412549393757 : ℝ) ≤ (66833899433679 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39477708086389 / 50000000000000 : ℝ) ≤ (66833899433679 / 100000000000000 : ℝ) := by
    have hw : (127412549393757 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (39477708086389 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (39477708086389 / 50000000000000 : ℝ) / (1 + (127412549393757 / 100000000000000 : ℝ)) = (78955416172778 / 227412549393757 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90245733245810661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 39477708086389 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 39477708086389 : ℝ) = (39477708086389 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 78955416172777 : ℝ) ≤ (23676537361901 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90245733245810661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39477708086389 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (78955416172777 / 100000000000000 : ℝ)) ≤ (23676537361901 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_546 : ∀ t : ℝ, (19948664777653 / 32000000000000 : ℝ) < t → t ≤ (39966122160243 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9772776282252140918690993 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (39966122160243 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_547
  have hV : (25409107201568864819141668490410513 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19948664777653 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_546 (Vfield_monotoneOn (show (19948664777653 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19948664777653 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_547 : (158954729873919475937008331591251 / 31250000000000000000000000000000 : ℝ) ≤ Vfield (39966122160243 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (39966122160243 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (493896599579 / 625000000000 : ℝ) ≤ Real.sqrt (39966122160243 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (39966122160243 / 64000000000000 : ℝ) ≤ (79023455932641 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (79023455932641 / 100000000000000 : ℝ) = (100000000000000 / 79023455932641 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (493896599579 / 625000000000 : ℝ) = (46875000000 / 493896599579 : ℝ) := by norm_num
  have hL1 : (24259100712747 / 50000000000000 : ℝ) ≤ Real.log (1 + (39966122160243 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((39966122160243 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46188363157129 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1549479528091 / 4459896542683 : ℝ) ≤ (10449343369379 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (79023455932641 / 100000000000000 : ℝ) ≤ (10449343369379 / 15625000000000 : ℝ) := by
    have hw : (127454723676833 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (79023455932641 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (79023455932641 / 100000000000000 : ℝ) / (1 + (127454723676833 / 100000000000000 : ℝ)) = (1549479528091 / 4459896542683 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90203835115464061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 79023455932641 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 79023455932641 : ℝ) = (79023455932641 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (46875000000 / 493896599579 : ℝ) ≤ (47312546431733 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90203835115464061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (79023455932641 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (493896599579 / 625000000000 : ℝ)) ≤ (47312546431733 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_547 : ∀ t : ℝ, (39966122160243 / 64000000000000 : ℝ) < t → t ≤ (2001745738259 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-77952881733108855898448251 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2001745738259 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_548
  have hV : (158954729873919475937008331591251 / 31250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (39966122160243 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_547 (Vfield_monotoneOn (show (39966122160243 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (39966122160243 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_548 : (12728193234487799494816941025895751 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (2001745738259 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2001745738259 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (39545718580079 / 50000000000000 : ℝ) ≤ Real.sqrt (2001745738259 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2001745738259 / 3200000000000 : ℝ) ≤ (79091437160159 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (79091437160159 / 100000000000000 : ℝ) = (100000000000000 / 79091437160159 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (39545718580079 / 50000000000000 : ℝ) = (3750000000000 / 39545718580079 : ℝ) := by norm_num
  have hL1 : (12146086958417 / 25000000000000 : ℝ) ≤ Real.log (1 + (2001745738259 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2001745738259 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-46017917820419 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (79091437160159 / 227496884009215 : ℝ) ≤ (334588159802649 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (79091437160159 / 100000000000000 : ℝ) ≤ (334588159802649 / 500000000000000 : ℝ) := by
    have hw : (25499376801843 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (79091437160159 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (79091437160159 / 100000000000000 : ℝ) / (1 + (25499376801843 / 20000000000000 : ℝ)) = (79091437160159 / 227496884009215 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90162000718959861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 79091437160159 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 79091437160159 : ℝ) = (79091437160159 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 39545718580079 : ℝ) ≤ (94544244047997 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90162000718959861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (79091437160159 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (39545718580079 / 50000000000000 : ℝ)) ≤ (94544244047997 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_548 : ∀ t : ℝ, (2001745738259 / 3200000000000 : ℝ) < t → t ≤ (40103707370117 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9715618189539403104386253 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (40103707370117 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_549
  have hV : (12728193234487799494816941025895751 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2001745738259 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_548 (Vfield_monotoneOn (show (2001745738259 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2001745738259 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_549 : (12739998158260907263881169162753523 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (40103707370117 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (40103707370117 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (39579680003067 / 50000000000000 : ℝ) ≤ Real.sqrt (40103707370117 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (40103707370117 / 64000000000000 : ℝ) ≤ (15831872001227 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (15831872001227 / 20000000000000 : ℝ) = (20000000000000 / 15831872001227 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (39579680003067 / 50000000000000 : ℝ) = (1250000000000 / 13193226667689 : ℝ) := by norm_num
  have hL1 : (48650450517289 / 100000000000000 : ℝ) ≤ Real.log (1 + (40103707370117 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((40103707370117 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-45847762505579 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (79159360006135 / 227539030404738 : ℝ) ≤ (167398507000479 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (15831872001227 / 20000000000000 : ℝ) ≤ (167398507000479 / 250000000000000 : ℝ) := by
    have hw : (63769515202369 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (15831872001227 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (15831872001227 / 20000000000000 : ℝ) / (1 + (63769515202369 / 50000000000000 : ℝ)) = (79159360006135 / 227539030404738 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90120229879298061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 15831872001227 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 15831872001227 : ℝ) = (15831872001227 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 13193226667689 : ℝ) ≤ (94463602115097 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90120229879298061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (15831872001227 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (39579680003067 / 50000000000000 : ℝ)) ≤ (94463602115097 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_549 : ∀ t : ℝ, (40103707370117 / 64000000000000 : ℝ) < t → t ≤ (20086249987527 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-38749176798918885136870473 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20086249987527 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_550
  have hV : (12739998158260907263881169162753523 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (40103707370117 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_549 (Vfield_monotoneOn (show (40103707370117 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (40103707370117 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_550 : (25503586369785102135431179341519449 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (20086249987527 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20086249987527 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (79227224620721 / 100000000000000 : ℝ) ≤ Real.sqrt (20086249987527 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20086249987527 / 32000000000000 : ℝ) ≤ (39613612310361 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39613612310361 / 50000000000000 : ℝ) = (50000000000000 / 39613612310361 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (79227224620721 / 100000000000000 : ℝ) = (7500000000000 / 79227224620721 : ℝ) := by norm_num
  have hL1 : (24358254767063 / 50000000000000 : ℝ) ≤ Real.log (1 + (20086249987527 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20086249987527 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-45677896227309 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (4401512478929 / 12643397937623 : ℝ) ≤ (3350055512963 / 10000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39613612310361 / 50000000000000 : ℝ) ≤ (3350055512963 / 5000000000000 : ℝ) := by
    have hw : (63790581438607 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (39613612310361 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (39613612310361 / 50000000000000 : ℝ) / (1 + (63790581438607 / 50000000000000 : ℝ)) = (4401512478929 / 12643397937623 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90078522420229661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 39613612310361 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 39613612310361 : ℝ) = (39613612310361 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 79227224620721 : ℝ) ≤ (1887663323679 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90078522420229661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39613612310361 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (79227224620721 / 100000000000000 : ℝ)) ≤ (1887663323679 / 20000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_550 : ∀ t : ℝ, (20086249987527 / 32000000000000 : ℝ) < t → t ≤ (40241292579991 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2414783176295062300046847 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (40241292579991 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_551
  have hV : (25503586369785102135431179341519449 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20086249987527 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_550 (Vfield_monotoneOn (show (20086249987527 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20086249987527 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_551 : (25527156675899215117913608636923439 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (40241292579991 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (40241292579991 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (79295031153431 / 100000000000000 : ℝ) ≤ Real.sqrt (40241292579991 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (40241292579991 / 64000000000000 : ℝ) ≤ (9911878894179 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9911878894179 / 12500000000000 : ℝ) = (12500000000000 / 9911878894179 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (79295031153431 / 100000000000000 : ℝ) = (7500000000000 / 79295031153431 : ℝ) := by norm_num
  have hL1 : (6097815617729 / 12500000000000 : ℝ) ≤ Real.log (1 + (40241292579991 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((40241292579991 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-45508318005323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (9911878894179 / 28452910180054 : ℝ) ≤ (335213772566211 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9911878894179 / 12500000000000 : ℝ) ≤ (335213772566211 / 500000000000000 : ℝ) := by
    have hw : (7976455090027 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (9911878894179 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (9911878894179 / 12500000000000 : ℝ) / (1 + (7976455090027 / 6250000000000 : ℝ)) = (9911878894179 / 28452910180054 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (90036878166247461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 9911878894179 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 9911878894179 : ℝ) = (9911878894179 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 79295031153431 : ℝ) ≤ (94302935378979 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (90036878166247461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9911878894179 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (79295031153431 / 100000000000000 : ℝ)) ≤ (94302935378979 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_551 : ∀ t : ℝ, (40241292579991 / 64000000000000 : ℝ) < t → t ≤ (1259690162029 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-7704902857956930224228963 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1259690162029 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_552
  have hV : (25527156675899215117913608636923439 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (40241292579991 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_551 (Vfield_monotoneOn (show (40241292579991 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (40241292579991 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_552 : (25550707281812759809781467336907353 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (1259690162029 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1259690162029 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (79362779753137 / 100000000000000 : ℝ) ≤ Real.sqrt (1259690162029 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1259690162029 / 2000000000000 : ℝ) ≤ (39681389876569 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39681389876569 / 50000000000000 : ℝ) = (50000000000000 / 39681389876569 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (79362779753137 / 100000000000000 : ℝ) = (7500000000000 / 79362779753137 : ℝ) := by norm_num
  have hL1 : (48848496797947 / 100000000000000 : ℝ) ≤ Real.log (1 + (1259690162029 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1259690162029 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5667378358039 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (39681389876569 / 113832693054079 : ℝ) ≤ (13416867147381 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39681389876569 / 50000000000000 : ℝ) ≤ (13416867147381 / 20000000000000 : ℝ) := by
    have hw : (63832693054079 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (39681389876569 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (39681389876569 / 50000000000000 : ℝ) / (1 + (63832693054079 / 50000000000000 : ℝ)) = (39681389876569 / 113832693054079 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89995296942584661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 39681389876569 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 39681389876569 : ℝ) = (39681389876569 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 79362779753137 : ℝ) ≤ (94222908829811 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89995296942584661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39681389876569 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (79362779753137 / 100000000000000 : ℝ)) ≤ (94222908829811 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_552 : ∀ t : ℝ, (1259690162029 / 2000000000000 : ℝ) < t → t ≤ (8075775557973 / 12800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9603277033091223694215147 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8075775557973 / 12800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_553
  have hV : (25550707281812759809781467336907353 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1259690162029 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_552 (Vfield_monotoneOn (show (1259690162029 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1259690162029 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_553 : (12787119117145336942814785991640991 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (8075775557973 / 12800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8075775557973 / 12800000000000 : ℝ) := by norm_num
  have hs1 : (39715235284039 / 50000000000000 : ℝ) ≤ Real.sqrt (8075775557973 / 12800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8075775557973 / 12800000000000 : ℝ) ≤ (79430470568079 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (79430470568079 / 100000000000000 : ℝ) = (100000000000000 / 79430470568079 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (39715235284039 / 50000000000000 : ℝ) = (3750000000000 / 39715235284039 : ℝ) := by norm_num
  have hL1 : (9782885031979 / 20000000000000 : ℝ) ≤ Real.log (1 + (8075775557973 / 12800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8075775557973 / 12800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-22585010916957 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (79430470568079 / 227707476894136 : ℝ) ≤ (167814635260703 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (79430470568079 / 100000000000000 : ℝ) ≤ (167814635260703 / 250000000000000 : ℝ) := by
    have hw : (15963434611767 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (79430470568079 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (79430470568079 / 100000000000000 : ℝ) / (1 + (15963434611767 / 12500000000000 : ℝ)) = (79430470568079 / 227707476894136 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89953778575208461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 79430470568079 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 79430470568079 : ℝ) = (79430470568079 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 39715235284039 : ℝ) ≤ (94143085671231 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89953778575208461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (79430470568079 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (39715235284039 / 50000000000000 : ℝ)) ≤ (94143085671231 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_553 : ∀ t : ℝ, (8075775557973 / 12800000000000 : ℝ) < t → t ≤ (20223835197401 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9575573645983631734831169 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (20223835197401 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_554
  have hV : (12787119117145336942814785991640991 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8075775557973 / 12800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_553 (Vfield_monotoneOn (show (8075775557973 / 12800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8075775557973 / 12800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_554 : (25597749579914746438439730380652109 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (20223835197401 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (20223835197401 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (79498103745861 / 100000000000000 : ℝ) ≤ Real.sqrt (20223835197401 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (20223835197401 / 32000000000000 : ℝ) ≤ (39749051872931 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39749051872931 / 50000000000000 : ℝ) = (50000000000000 / 39749051872931 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (79498103745861 / 100000000000000 : ℝ) = (2500000000000 / 26499367915287 : ℝ) := by norm_num
  have hL1 : (48980310084991 / 100000000000000 : ℝ) ≤ Real.log (1 + (20223835197401 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((20223835197401 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-45001301948677 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (79498103745862 / 227749553812089 : ℝ) ≤ (167918274471679 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39749051872931 / 50000000000000 : ℝ) ≤ (167918274471679 / 250000000000000 : ℝ) := by
    have hw : (127749553812089 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (39749051872931 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (39749051872931 / 50000000000000 : ℝ) / (1 + (127749553812089 / 100000000000000 : ℝ)) = (79498103745862 / 227749553812089 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89912322890818061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 39749051872931 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 39749051872931 : ℝ) = (39749051872931 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 26499367915287 : ℝ) ≤ (94063465043149 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89912322890818061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39749051872931 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (79498103745861 / 100000000000000 : ℝ)) ≤ (94063465043149 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_554 : ∀ t : ℝ, (20223835197401 / 32000000000000 : ℝ) < t → t ≤ (40516462999739 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-76384114116179452917696233 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (40516462999739 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_555
  have hV : (25597749579914746438439730380652109 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (20223835197401 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_554 (Vfield_monotoneOn (show (20223835197401 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (20223835197401 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_555 : (12810620682542287317685352990372677 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (40516462999739 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (40516462999739 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (39782839716733 / 50000000000000 : ℝ) ≤ Real.sqrt (40516462999739 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (40516462999739 / 64000000000000 : ℝ) ≤ (79565679433467 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (79565679433467 / 100000000000000 : ℝ) = (100000000000000 / 79565679433467 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (39782839716733 / 50000000000000 : ℝ) = (3750000000000 / 39782839716733 : ℝ) := by norm_num
  have hL1 : (1532692238451 / 3125000000000 : ℝ) ≤ Real.log (1 + (40516462999739 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((40516462999739 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-11208216562007 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (8840631048163 / 25310179652857 : ℝ) ≤ (336043514813259 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (79565679433467 / 100000000000000 : ℝ) ≤ (336043514813259 / 500000000000000 : ℝ) := by
    have hw : (127791616875713 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (79565679433467 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (79565679433467 / 100000000000000 : ℝ) / (1 + (127791616875713 / 100000000000000 : ℝ)) = (8840631048163 / 25310179652857 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89870929716837861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 79565679433467 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 79565679433467 : ℝ) = (79565679433467 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 39782839716733 : ℝ) ≤ (46992023045279 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89870929716837861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (79565679433467 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (39782839716733 / 50000000000000 : ℝ)) ≤ (46992023045279 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_555 : ∀ t : ℝ, (40516462999739 / 64000000000000 : ℝ) < t → t ≤ (10146313901169 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9520595008025418284536881 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (10146313901169 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_556
  have hV : (12810620682542287317685352990372677 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (40516462999739 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_555 (Vfield_monotoneOn (show (40516462999739 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (40516462999739 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_556 : (102578854544077038840626553527821 / 20000000000000000000000000000000 : ℝ) ≤ Vfield (10146313901169 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (10146313901169 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (318532791109 / 400000000000 : ℝ) ≤ Real.sqrt (10146313901169 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (10146313901169 / 16000000000000 : ℝ) ≤ (79633197777251 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (79633197777251 / 100000000000000 : ℝ) = (100000000000000 / 79633197777251 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (318532791109 / 400000000000 : ℝ) = (30000000000 / 318532791109 : ℝ) := by norm_num
  have hL1 : (9822389970661 / 20000000000000 : ℝ) ≤ Real.log (1 + (10146313901169 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((10146313901169 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-558308922203 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (79633197777251 / 227833666098687 : ℝ) ≤ (336250168990369 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (79633197777251 / 100000000000000 : ℝ) ≤ (336250168990369 / 500000000000000 : ℝ) := by
    have hw : (127833666098687 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (79633197777251 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (79633197777251 / 100000000000000 : ℝ) / (1 + (127833666098687 / 100000000000000 : ℝ)) = (79633197777251 / 227833666098687 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89829598881415861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 79633197777251 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 79633197777251 : ℝ) = (79633197777251 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (30000000000 / 318532791109 : ℝ) ≤ (18780965592699 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89829598881415861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (79633197777251 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (318532791109 / 400000000000 : ℝ)) ≤ (18780965592699 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_556 : ∀ t : ℝ, (10146313901169 / 16000000000000 : ℝ) < t → t ≤ (40654048209613 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-75946497893184585471326461 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (40654048209613 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_557
  have hV : (102578854544077038840626553527821 / 20000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (10146313901169 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_556 (Vfield_monotoneOn (show (10146313901169 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (10146313901169 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_557 : (25668166438756676365074536121941243 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (40654048209613 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (40654048209613 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (79700658922947 / 100000000000000 : ℝ) ≤ Real.sqrt (40654048209613 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (40654048209613 / 64000000000000 : ℝ) ≤ (19925164730737 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19925164730737 / 25000000000000 : ℝ) = (25000000000000 / 19925164730737 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (79700658922947 / 100000000000000 : ℝ) = (2500000000000 / 26566886307649 : ℝ) := by norm_num
  have hL1 : (24588852405291 / 50000000000000 : ℝ) ≤ Real.log (1 + (40654048209613 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((40654048209613 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-44496843582399 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (39850329461474 / 113937850747331 : ℝ) ≤ (168228256165177 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19925164730737 / 25000000000000 : ℝ) ≤ (168228256165177 / 250000000000000 : ℝ) := by
    have hw : (63937850747331 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (19925164730737 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (19925164730737 / 25000000000000 : ℝ) / (1 + (63937850747331 / 50000000000000 : ℝ)) = (39850329461474 / 113937850747331 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89788330213418861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 19925164730737 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 19925164730737 : ℝ) = (19925164730737 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 26566886307649 : ℝ) ≤ (18765161963401 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89788330213418861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19925164730737 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (79700658922947 / 100000000000000 : ℝ)) ≤ (18765161963401 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_557 : ∀ t : ℝ, (40654048209613 / 64000000000000 : ℝ) < t → t ≤ (814456816291 / 1280000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-75729300234507830528632307 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (814456816291 / 1280000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_558
  have hV : (25668166438756676365074536121941243 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (40654048209613 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_557 (Vfield_monotoneOn (show (40654048209613 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (40654048209613 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_558 : (25691599819157190530371878943072151 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (814456816291 / 1280000000000 : ℝ) := by
  have hp : (0 : ℝ) < (814456816291 / 1280000000000 : ℝ) := by norm_num
  have hs1 : (79768063015679 / 100000000000000 : ℝ) ≤ Real.sqrt (814456816291 / 1280000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (814456816291 / 1280000000000 : ℝ) ≤ (62318799231 / 78125000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (62318799231 / 78125000000 : ℝ) = (78125000000 / 62318799231 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (79768063015679 / 100000000000000 : ℝ) = (7500000000000 / 79768063015679 : ℝ) := by norm_num
  have hL1 : (24621708279563 / 50000000000000 : ℝ) ≤ Real.log (1 + (814456816291 / 1280000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((814456816291 / 1280000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-44329254720371 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (79768063015680 / 227917723077271 : ℝ) ≤ (168331272842659 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (62318799231 / 78125000000 : ℝ) ≤ (168331272842659 / 250000000000000 : ℝ) := by
    have hw : (127917723077271 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (62318799231 / 78125000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (62318799231 / 78125000000 : ℝ) / (1 + (127917723077271 / 100000000000000 : ℝ)) = (79768063015680 / 227917723077271 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89747123542426061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (78125000000 / 62318799231 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (78125000000 / 62318799231 : ℝ) = (62318799231 / 78125000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 79768063015679 : ℝ) ≤ (93746990811101 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89747123542426061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (62318799231 / 78125000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (79768063015679 / 100000000000000 : ℝ)) ≤ (93746990811101 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_558 : ∀ t : ℝ, (814456816291 / 1280000000000 : ℝ) < t → t ≤ (40791633419487 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-75513141315292850190152243 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (40791633419487 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_559
  have hV : (25691599819157190530371878943072151 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (814456816291 / 1280000000000 : ℝ) := by norm_num
    refine le_trans V_pt_558 (Vfield_monotoneOn (show (814456816291 / 1280000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (814456816291 / 1280000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_559 : (25715013822902277815628807726268857 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (40791633419487 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (40791633419487 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (79835410199953 / 100000000000000 : ℝ) ≤ Real.sqrt (40791633419487 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (40791633419487 / 64000000000000 : ℝ) ≤ (39917705099977 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (39917705099977 / 50000000000000 : ℝ) = (50000000000000 / 39917705099977 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (79835410199953 / 100000000000000 : ℝ) = (7500000000000 / 79835410199953 : ℝ) := by norm_num
  have hL1 : (24654542577843 / 50000000000000 : ℝ) ≤ Real.log (1 + (40791633419487 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((40791633419487 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-11040486562193 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (39917705099977 / 113979865430061 : ℝ) ≤ (336868269903811 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (39917705099977 / 50000000000000 : ℝ) ≤ (336868269903811 / 500000000000000 : ℝ) := by
    have hw : (63979865430061 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (39917705099977 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (39917705099977 / 50000000000000 : ℝ) / (1 + (63979865430061 / 50000000000000 : ℝ)) = (39917705099977 / 113979865430061 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (89705978698727461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 39917705099977 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 39917705099977 : ℝ) = (39917705099977 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 79835410199953 : ℝ) ≤ (93668370110727 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (89705978698727461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (39917705099977 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (79835410199953 / 100000000000000 : ℝ)) ≤ (93668370110727 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_559 : ∀ t : ℝ, (40791633419487 / 64000000000000 : ℝ) < t → t ≤ (5107553253053 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-37648998407042027591661681 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (5107553253053 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_560
  have hV : (25715013822902277815628807726268857 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (40791633419487 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_559 (Vfield_monotoneOn (show (40791633419487 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (40791633419487 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
