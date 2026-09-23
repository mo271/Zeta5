import Apery.Table2.U11
import Apery.Table2.U12

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_440 : (10815936239748573317700351629061603 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1853008205557 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1853008205557 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (34031311001387 / 50000000000000 : ℝ) ≤ Real.sqrt (1853008205557 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1853008205557 / 4000000000000 : ℝ) ≤ (2722504880111 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2722504880111 / 4000000000000 : ℝ) = (4000000000000 / 2722504880111 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (34031311001387 / 50000000000000 : ℝ) = (3750000000000 / 34031311001387 : ℝ) := by norm_num
  have hL1 : (19033069556429 / 50000000000000 : ℝ) ≤ Real.log (1 + (1853008205557 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1853008205557 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-75741469493939 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68062622002775 / 220964955726411 : ℝ) ≤ (298802373663551 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2722504880111 / 4000000000000 : ℝ) ≤ (298802373663551 / 500000000000000 : ℝ) := by
    have hw : (120964955726411 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (2722504880111 / 4000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2722504880111 / 4000000000000 : ℝ) / (1 + (120964955726411 / 100000000000000 : ℝ)) = (68062622002775 / 220964955726411 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97319157946779461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 2722504880111 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 2722504880111 : ℝ) = (2722504880111 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 34031311001387 : ℝ) ≤ (109749859654589 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97319157946779461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2722504880111 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (34031311001387 / 50000000000000 : ℝ)) ≤ (109749859654589 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_440 : ∀ t : ℝ, (1853008205557 / 4000000000000 : ℝ) < t → t ≤ (185565680531 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-116053690269002814487821633 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (185565680531 / 400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_441
  have hV : (10815936239748573317700351629061603 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1853008205557 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_440 (Vfield_monotoneOn (show (1853008205557 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1853008205557 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_441 : (21648679106125115322090487132012739 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (185565680531 / 400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (185565680531 / 400000000000 : ℝ) := by norm_num
  have hs1 : (68111247333131 / 100000000000000 : ℝ) ≤ Real.sqrt (185565680531 / 400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (185565680531 / 400000000000 : ℝ) ≤ (17027811833283 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17027811833283 / 25000000000000 : ℝ) = (25000000000000 / 17027811833283 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (68111247333131 / 100000000000000 : ℝ) = (7500000000000 / 68111247333131 : ℝ) := by norm_num
  have hL1 : (4763922602139 / 12500000000000 : ℝ) ≤ Real.log (1 + (185565680531 / 400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((185565680531 / 400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-75600348739429 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68111247333132 / 220992322125311 : ℝ) ≤ (298968491090091 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17027811833283 / 25000000000000 : ℝ) ≤ (298968491090091 / 500000000000000 : ℝ) := by
    have hw : (120992322125311 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (17027811833283 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17027811833283 / 25000000000000 : ℝ) / (1 + (120992322125311 / 100000000000000 : ℝ)) = (68111247333132 / 220992322125311 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97285934461471461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 17027811833283 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 17027811833283 : ℝ) = (17027811833283 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 68111247333131 : ℝ) ≤ (877377080557 / 8000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97285934461471461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17027811833283 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (68111247333131 / 100000000000000 : ℝ)) ≤ (877377080557 / 8000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_441 : ∀ t : ℝ, (185565680531 / 400000000000 : ℝ) < t → t ≤ (1858305405063 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-7243284087588102940861383 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1858305405063 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_442
  have hV : (21648679106125115322090487132012739 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (185565680531 / 400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_441 (Vfield_monotoneOn (show (185565680531 / 400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (185565680531 / 400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_442 : (10832737196540866298888367612191833 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1858305405063 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1858305405063 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (34079918987057 / 50000000000000 : ℝ) ≤ Real.sqrt (1858305405063 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1858305405063 / 4000000000000 : ℝ) ≤ (13631967594823 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13631967594823 / 20000000000000 : ℝ) = (20000000000000 / 13631967594823 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (34079918987057 / 50000000000000 : ℝ) = (3750000000000 / 34079918987057 : ℝ) := by norm_num
  have hL1 : (4769575257813 / 12500000000000 : ℝ) ≤ Real.log (1 + (1858305405063 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1858305405063 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-75459426854979 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68159837974115 / 221019682335798 : ℝ) ≤ (18695900933841 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13631967594823 / 20000000000000 : ℝ) ≤ (18695900933841 / 31250000000000 : ℝ) := by
    have hw : (60509841167899 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (13631967594823 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (13631967594823 / 20000000000000 : ℝ) / (1 + (60509841167899 / 50000000000000 : ℝ)) = (68159837974115 / 221019682335798 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97252749691198461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 13631967594823 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 13631967594823 : ℝ) = (13631967594823 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 34079918987057 : ℝ) ≤ (13699321923291 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97252749691198461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13631967594823 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (34079918987057 / 50000000000000 : ℝ)) ≤ (13699321923291 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_442 : ∀ t : ℝ, (1858305405063 / 4000000000000 : ℝ) < t → t ≤ (116309625301 / 250000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-28933024424771214376024659 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (116309625301 / 250000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_443
  have hV : (10832737196540866298888367612191833 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1858305405063 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_442 (Vfield_monotoneOn (show (1858305405063 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1858305405063 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_443 : (10841129181073170763593564872010401 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (116309625301 / 250000000000 : ℝ) := by
  have hp : (0 : ℝ) < (116309625301 / 250000000000 : ℝ) := by norm_num
  have hs1 : (34104196999929 / 50000000000000 : ℝ) ≤ Real.sqrt (116309625301 / 250000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (116309625301 / 250000000000 : ℝ) ≤ (68208393999859 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (68208393999859 / 100000000000000 : ℝ) = (100000000000000 / 68208393999859 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (34104196999929 / 50000000000000 : ℝ) = (1250000000000 / 11368065666643 : ℝ) := by norm_num
  have hL1 : (38201802867529 / 100000000000000 : ℝ) ≤ Real.log (1 + (116309625301 / 250000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((116309625301 / 250000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-37659351640437 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68208393999859 / 221047036362068 : ℝ) ≤ (11972005825827 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (68208393999859 / 100000000000000 : ℝ) ≤ (11972005825827 / 20000000000000 : ℝ) := by
    have hw : (30261759090517 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (68208393999859 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (68208393999859 / 100000000000000 : ℝ) / (1 + (30261759090517 / 25000000000000 : ℝ)) = (68208393999859 / 221047036362068 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97219603550354661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 68208393999859 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 68208393999859 : ℝ) = (68208393999859 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 11368065666643 : ℝ) ≤ (5475859001121 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97219603550354661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (68208393999859 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (34104196999929 / 50000000000000 : ℝ)) ≤ (5475859001121 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_443 : ∀ t : ℝ, (116309625301 / 250000000000 : ℝ) < t → t ≤ (1863602604569 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-115572333403060338461274793 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1863602604569 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_444
  have hV : (10841129181073170763593564872010401 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (116309625301 / 250000000000 : ℝ) := by norm_num
    refine le_trans V_pt_443 (Vfield_monotoneOn (show (116309625301 / 250000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (116309625301 / 250000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_444 : (10849515517515166667070627680904511 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (1863602604569 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1863602604569 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (34128457742119 / 50000000000000 : ℝ) ≤ Real.sqrt (1863602604569 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1863602604569 / 4000000000000 : ℝ) ≤ (68256915484239 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (68256915484239 / 100000000000000 : ℝ) = (100000000000000 / 68256915484239 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (34128457742119 / 50000000000000 : ℝ) = (3750000000000 / 34128457742119 : ℝ) := by norm_num
  have hL1 : (1195218226583 / 3125000000000 : ℝ) ≤ Real.log (1 + (1863602604569 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1863602604569 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-75178177459759 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68256915484239 / 221074384208314 : ℝ) ≤ (149732841814657 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (68256915484239 / 100000000000000 : ℝ) ≤ (149732841814657 / 250000000000000 : ℝ) := by
    have hw : (60537192104157 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (68256915484239 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (68256915484239 / 100000000000000 : ℝ) / (1 + (60537192104157 / 50000000000000 : ℝ)) = (68256915484239 / 221074384208314 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97186495953626861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 68256915484239 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 68256915484239 : ℝ) = (68256915484239 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 34128457742119 : ℝ) ≤ (27359987099623 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97186495953626861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (68256915484239 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (34128457742119 / 50000000000000 : ℝ)) ≤ (27359987099623 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_444 : ∀ t : ℝ, (1863602604569 / 4000000000000 : ℝ) < t → t ≤ (933125602161 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-57706619672919614060800461 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (933125602161 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_445
  have hV : (10849515517515166667070627680904511 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1863602604569 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_444 (Vfield_monotoneOn (show (1863602604569 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1863602604569 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_445 : (21715792433375128373154929731018647 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (933125602161 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (933125602161 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (68305402500863 / 100000000000000 : ℝ) ≤ Real.sqrt (933125602161 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (933125602161 / 2000000000000 : ℝ) ≤ (266817978519 / 390625000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (266817978519 / 390625000000 : ℝ) = (390625000000 / 266817978519 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (68305402500863 / 100000000000000 : ℝ) = (7500000000000 / 68305402500863 : ℝ) := by norm_num
  have hL1 : (38292143230331 / 100000000000000 : ℝ) ≤ Real.log (1 + (933125602161 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((933125602161 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-37518924418313 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (22768467500288 / 73700575292907 : ℝ) ≤ (74907757329363 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (266817978519 / 390625000000 : ℝ) ≤ (74907757329363 / 125000000000000 : ℝ) := by
    have hw : (121101725878721 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (266817978519 / 390625000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (266817978519 / 390625000000 : ℝ) / (1 + (121101725878721 / 100000000000000 : ℝ)) = (22768467500288 / 73700575292907 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97153426815999261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (390625000000 / 266817978519 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (390625000000 / 266817978519 : ℝ) = (266817978519 / 390625000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 68305402500863 : ℝ) ≤ (21872575987599 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97153426815999261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (266817978519 / 390625000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (68305402500863 / 100000000000000 : ℝ)) ≤ (21872575987599 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_445 : ∀ t : ℝ, (933125602161 / 2000000000000 : ℝ) < t → t ≤ (467887100957 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-115097012013816049005483359 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (467887100957 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_446
  have hV : (21715792433375128373154929731018647 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (933125602161 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_445 (Vfield_monotoneOn (show (933125602161 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (933125602161 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_446 : (21749281492672129092969900980441003 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (467887100957 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (467887100957 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (68402273423987 / 100000000000000 : ℝ) ≤ Real.sqrt (467887100957 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (467887100957 / 1000000000000 : ℝ) ≤ (17100568355997 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17100568355997 / 25000000000000 : ℝ) = (25000000000000 / 17100568355997 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (68402273423987 / 100000000000000 : ℝ) = (7500000000000 / 68402273423987 : ℝ) := by norm_num
  have hL1 : (38382402052981 / 100000000000000 : ℝ) ≤ Real.log (1 + (467887100957 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((467887100957 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-74757780975929 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (17100568355997 / 55289097677186 : ℝ) ≤ (37495143187531 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17100568355997 / 25000000000000 : ℝ) ≤ (37495143187531 / 62500000000000 : ℝ) := by
    have hw : (15144548838593 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (17100568355997 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17100568355997 / 25000000000000 : ℝ) / (1 + (15144548838593 / 12500000000000 : ℝ)) = (17100568355997 / 55289097677186 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97087403579440061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 17100568355997 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 17100568355997 : ℝ) = (17100568355997 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 68402273423987 : ℝ) ≤ (109209230215273 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97087403579440061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17100568355997 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (68402273423987 / 100000000000000 : ℝ)) ≤ (109209230215273 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_446 : ∀ t : ℝ, (467887100957 / 1000000000000 : ℝ) < t → t ≤ (938422801667 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2869583021118950878138561 / 2500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (938422801667 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_447
  have hV : (21749281492672129092969900980441003 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (467887100957 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_446 (Vfield_monotoneOn (show (467887100957 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (467887100957 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_447 : (21782725711806501311328052071238173 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (938422801667 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (938422801667 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (68499007352917 / 100000000000000 : ℝ) ≤ Real.sqrt (938422801667 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (938422801667 / 2000000000000 : ℝ) ≤ (34249503676459 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34249503676459 / 50000000000000 : ℝ) = (50000000000000 / 34249503676459 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (68499007352917 / 100000000000000 : ℝ) = (7500000000000 / 68499007352917 : ℝ) := by norm_num
  have hL1 : (19236289741269 / 50000000000000 : ℝ) ≤ Real.log (1 + (938422801667 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((938422801667 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9309811913143 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68499007352918 / 221211030885539 : ℝ) ≤ (300290497565557 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34249503676459 / 50000000000000 : ℝ) ≤ (300290497565557 / 500000000000000 : ℝ) := by
    have hw : (121211030885539 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (34249503676459 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (34249503676459 / 50000000000000 : ℝ) / (1 + (121211030885539 / 100000000000000 : ℝ)) = (68499007352918 / 221211030885539 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (97021533166378261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 34249503676459 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 34249503676459 : ℝ) = (34249503676459 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 68499007352917 : ℝ) ≤ (109056226298293 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (97021533166378261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34249503676459 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (68499007352917 / 100000000000000 : ℝ)) ≤ (109056226298293 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_447 : ∀ t : ℝ, (938422801667 / 2000000000000 : ℝ) < t → t ≤ (47053570071 / 100000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-57236039170442310837620061 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (47053570071 / 100000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_448
  have hV : (21782725711806501311328052071238173 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (938422801667 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_447 (Vfield_monotoneOn (show (938422801667 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (938422801667 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_448 : (21816125261463548681360473475577949 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (47053570071 / 100000000000 : ℝ) := by
  have hp : (0 : ℝ) < (47053570071 / 100000000000 : ℝ) := by norm_num
  have hs1 : (68595604867221 / 100000000000000 : ℝ) ≤ Real.sqrt (47053570071 / 100000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (47053570071 / 100000000000 : ℝ) ≤ (34297802433611 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34297802433611 / 50000000000000 : ℝ) = (50000000000000 / 34297802433611 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (68595604867221 / 100000000000000 : ℝ) = (2500000000000 / 22865201622407 : ℝ) := by norm_num
  have hL1 : (9640668916417 / 25000000000000 : ℝ) ≤ Real.log (1 + (47053570071 / 100000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((47053570071 / 100000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-74199987467347 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (34297802433611 / 110632823221214 : ℝ) ≤ (150309544430877 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34297802433611 / 50000000000000 : ℝ) ≤ (150309544430877 / 250000000000000 : ℝ) := by
    have hw : (30316411610607 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (34297802433611 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (34297802433611 / 50000000000000 : ℝ) / (1 + (30316411610607 / 25000000000000 : ℝ)) = (34297802433611 / 110632823221214 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96955814907138861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 34297802433611 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 34297802433611 : ℝ) = (34297802433611 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 22865201622407 : ℝ) ≤ (54451931837831 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96955814907138861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34297802433611 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (68595604867221 / 100000000000000 : ℝ)) ≤ (54451931837831 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_448 : ∀ t : ℝ, (47053570071 / 100000000000 : ℝ) < t → t ≤ (943720001173 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-3567600110396224013932101 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (943720001173 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_449
  have hV : (21816125261463548681360473475577949 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (47053570071 / 100000000000 : ℝ) := by norm_num
    refine le_trans V_pt_448 (Vfield_monotoneOn (show (47053570071 / 100000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (47053570071 / 100000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_449 : (5462370077814213777339416482390631 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (943720001173 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (943720001173 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (17173016635599 / 25000000000000 : ℝ) ≤ Real.sqrt (943720001173 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (943720001173 / 2000000000000 : ℝ) ≤ (68692066542397 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (68692066542397 / 100000000000000 : ℝ) = (100000000000000 / 68692066542397 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17173016635599 / 25000000000000 : ℝ) = (625000000000 / 5724338878533 : ℝ) := by norm_num
  have hL1 : (19326345374319 / 50000000000000 : ℝ) ≤ Real.log (1 + (943720001173 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((943720001173 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-73922253141913 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68692066542397 / 221320237412663 : ℝ) ≤ (75236730678583 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (68692066542397 / 100000000000000 : ℝ) ≤ (75236730678583 / 125000000000000 : ℝ) := by
    have hw : (121320237412663 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (68692066542397 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (68692066542397 / 100000000000000 : ℝ) / (1 + (121320237412663 / 100000000000000 : ℝ)) = (68692066542397 / 221320237412663 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96890248136623261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 68692066542397 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 68692066542397 : ℝ) = (68692066542397 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (625000000000 / 5724338878533 : ℝ) ≤ (108752137879977 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96890248136623261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (68692066542397 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17173016635599 / 25000000000000 : ℝ)) ≤ (108752137879977 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_449 : ∀ t : ℝ, (943720001173 / 2000000000000 : ℝ) < t → t ≤ (473184300463 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-113856621265784395529632851 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (473184300463 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_450
  have hV : (5462370077814213777339416482390631 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (943720001173 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_449 (Vfield_monotoneOn (show (943720001173 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (943720001173 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_450 : (21882791029735311778288403304958869 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (473184300463 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (473184300463 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (68788392949901 / 100000000000000 : ℝ) ≤ Real.sqrt (473184300463 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (473184300463 / 1000000000000 : ℝ) ≤ (34394196474951 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34394196474951 / 50000000000000 : ℝ) = (50000000000000 / 34394196474951 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (68788392949901 / 100000000000000 : ℝ) = (7500000000000 / 68788392949901 : ℝ) := by norm_num
  have hL1 : (38742624877323 / 100000000000000 : ℝ) ≤ Real.log (1 + (473184300463 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((473184300463 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-36822644022059 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (22929464316634 / 73791601276473 : ℝ) ≤ (301274002426103 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34394196474951 / 50000000000000 : ℝ) ≤ (301274002426103 / 500000000000000 : ℝ) := by
    have hw : (121374803829419 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (34394196474951 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (34394196474951 / 50000000000000 : ℝ) / (1 + (121374803829419 / 100000000000000 : ℝ)) = (22929464316634 / 73791601276473 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96824832194269061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 34394196474951 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 34394196474951 : ℝ) = (34394196474951 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 68788392949901 : ℝ) ≤ (108601044487289 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96824832194269061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34394196474951 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (68788392949901 / 100000000000000 : ℝ)) ≤ (108601044487289 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_450 : ∀ t : ℝ, (473184300463 / 1000000000000 : ℝ) < t → t ≤ (949017200679 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-113552261586718222927587569 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (949017200679 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_451
  have hV : (21882791029735311778288403304958869 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (473184300463 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_450 (Vfield_monotoneOn (show (473184300463 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (473184300463 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_451 : (54790143960983714386107782558467 / 12500000000000000000000000000000 : ℝ) ≤ Vfield (949017200679 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (949017200679 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (172211461643 / 250000000000 : ℝ) ≤ Real.sqrt (949017200679 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (949017200679 / 2000000000000 : ℝ) ≤ (68884584657201 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (68884584657201 / 100000000000000 : ℝ) = (100000000000000 / 68884584657201 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (172211461643 / 250000000000 : ℝ) = (18750000000 / 172211461643 : ℝ) := by norm_num
  have hL1 : (38832478197201 / 100000000000000 : ℝ) ≤ Real.log (1 + (949017200679 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((949017200679 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-73369087924741 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68884584657201 / 221429345725796 : ℝ) ≤ (301600331277421 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (68884584657201 / 100000000000000 : ℝ) ≤ (301600331277421 / 500000000000000 : ℝ) := by
    have hw : (30357336431449 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (68884584657201 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (68884584657201 / 100000000000000 : ℝ) / (1 + (30357336431449 / 25000000000000 : ℝ)) = (68884584657201 / 221429345725796 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96759566424005461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 68884584657201 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 68884584657201 : ℝ) = (68884584657201 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (18750000000 / 172211461643 : ℝ) ≤ (54225289558277 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96759566424005461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (68884584657201 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (172211461643 / 250000000000 : ℝ)) ≤ (54225289558277 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_451 : ∀ t : ℝ, (949017200679 / 2000000000000 : ℝ) < t → t ≤ (59479112527 / 125000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-113250059211103421236204441 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (59479112527 / 125000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_452
  have hV : (54790143960983714386107782558467 / 12500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (949017200679 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_451 (Vfield_monotoneOn (show (949017200679 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (949017200679 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_452 : (21949280141681151147893285704563969 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (59479112527 / 125000000000 : ℝ) := by
  have hp : (0 : ℝ) < (59479112527 / 125000000000 : ℝ) := by norm_num
  have hs1 : (68980642227801 / 100000000000000 : ℝ) ≤ Real.sqrt (59479112527 / 125000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (59479112527 / 125000000000 : ℝ) ≤ (34490321113901 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (34490321113901 / 50000000000000 : ℝ) = (50000000000000 / 34490321113901 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (68980642227801 / 100000000000000 : ℝ) = (2500000000000 / 22993547409267 : ℝ) := by norm_num
  have hL1 : (38922250853363 / 100000000000000 : ℝ) ≤ Real.log (1 + (59479112527 / 125000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((59479112527 / 125000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-36546824284837 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (68980642227802 / 221483863134821 : ℝ) ≤ (301925912526397 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (34490321113901 / 50000000000000 : ℝ) ≤ (301925912526397 / 500000000000000 : ℝ) := by
    have hw : (121483863134821 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (34490321113901 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (34490321113901 / 50000000000000 : ℝ) / (1 + (121483863134821 / 100000000000000 : ℝ)) = (68980642227802 / 221483863134821 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96694450174210261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 34490321113901 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 34490321113901 : ℝ) = (34490321113901 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 22993547409267 : ℝ) ≤ (54150368714551 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96694450174210261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (34490321113901 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (68980642227801 / 100000000000000 : ℝ)) ≤ (54150368714551 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_452 : ∀ t : ℝ, (59479112527 / 125000000000 : ℝ) < t → t ≤ (190862880037 / 400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-112949953061183410715971841 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (190862880037 / 400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_453
  have hV : (21949280141681151147893285704563969 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (59479112527 / 125000000000 : ℝ) := by norm_num
    refine le_trans V_pt_452 (Vfield_monotoneOn (show (59479112527 / 125000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (59479112527 / 125000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_453 : (4396491773402429591760802203550171 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (190862880037 / 400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (190862880037 / 400000000000 : ℝ) := by norm_num
  have hs1 : (13815313244259 / 20000000000000 : ℝ) ≤ Real.sqrt (190862880037 / 400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (190862880037 / 400000000000 : ℝ) ≤ (4317285388831 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4317285388831 / 6250000000000 : ℝ) = (6250000000000 / 4317285388831 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (13815313244259 / 20000000000000 : ℝ) = (500000000000 / 4605104414753 : ℝ) := by norm_num
  have hL1 : (7802388598101 / 20000000000000 : ℝ) ≤ Real.log (1 + (190862880037 / 400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((190862880037 / 400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-14563793159907 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (34538283110648 / 110769178044723 : ℝ) ≤ (151125374704557 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4317285388831 / 6250000000000 : ℝ) ≤ (151125374704557 / 250000000000000 : ℝ) := by
    have hw : (60769178044723 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (4317285388831 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (4317285388831 / 6250000000000 : ℝ) / (1 + (60769178044723 / 50000000000000 : ℝ)) = (34538283110648 / 110769178044723 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96629482797666861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 4317285388831 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 4317285388831 : ℝ) = (4317285388831 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4605104414753 : ℝ) ≤ (27037878782027 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96629482797666861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4317285388831 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (13815313244259 / 20000000000000 : ℝ)) ≤ (27037878782027 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_453 : ∀ t : ℝ, (190862880037 / 400000000000 : ℝ) < t → t ≤ (478481499969 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-112651885861845267059075253 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (478481499969 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_454
  have hV : (4396491773402429591760802203550171 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (190862880037 / 400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_453 (Vfield_monotoneOn (show (190862880037 / 400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (190862880037 / 400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_454 : (2201559392477229435507657597686691 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (478481499969 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (478481499969 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (6917235719339 / 10000000000000 : ℝ) ≤ Real.sqrt (478481499969 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (478481499969 / 1000000000000 : ℝ) ≤ (69172357193391 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (69172357193391 / 100000000000000 : ℝ) = (100000000000000 / 69172357193391 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6917235719339 / 10000000000000 : ℝ) = (750000000000 / 6917235719339 : ℝ) := by norm_num
  have hL1 : (39101554752937 / 100000000000000 : ℝ) ≤ Real.log (1 + (478481499969 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((478481499969 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-72545035469287 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1002497930339 / 3211490211921 : ℝ) ≤ (151287422569907 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (69172357193391 / 100000000000000 : ℝ) ≤ (151287422569907 / 250000000000000 : ℝ) := by
    have hw : (121592824622549 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (69172357193391 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (69172357193391 / 100000000000000 : ℝ) / (1 + (121592824622549 / 100000000000000 : ℝ)) = (1002497930339 / 3211490211921 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96564663651526861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 69172357193391 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 69172357193391 : ℝ) = (69172357193391 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 6917235719339 : ℝ) ≤ (108002907958083 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96564663651526861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (69172357193391 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6917235719339 / 10000000000000 : ℝ)) ≤ (108002907958083 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_454 : ∀ t : ℝ, (478481499969 / 1000000000000 : ℝ) < t → t ≤ (959611599691 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-112355803786295915367659197 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (959611599691 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_455
  have hV : (2201559392477229435507657597686691 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (478481499969 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_454 (Vfield_monotoneOn (show (478481499969 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (478481499969 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_455 : (11024342739165040005921118397839313 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (959611599691 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (959611599691 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (34634007847977 / 50000000000000 : ℝ) ≤ Real.sqrt (959611599691 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (959611599691 / 2000000000000 : ℝ) ≤ (13853603139191 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (13853603139191 / 20000000000000 : ℝ) = (20000000000000 / 13853603139191 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (34634007847977 / 50000000000000 : ℝ) = (1250000000000 / 11544669282659 : ℝ) := by norm_num
  have hL1 : (1959554314229 / 5000000000000 : ℝ) ≤ Real.log (1 + (959611599691 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((959611599691 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9033981683483 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (13853603139191 / 44329453753387 : ℝ) ≤ (302898202911127 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (13853603139191 / 20000000000000 : ℝ) ≤ (302898202911127 / 500000000000000 : ℝ) := by
    have hw : (24329453753387 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (13853603139191 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (13853603139191 / 20000000000000 : ℝ) / (1 + (24329453753387 / 20000000000000 : ℝ)) = (13853603139191 / 44329453753387 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96499992097264261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 13853603139191 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 13853603139191 : ℝ) = (13853603139191 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 11544669282659 : ℝ) ≤ (53927455852177 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96499992097264261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (13853603139191 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (34634007847977 / 50000000000000 : ℝ)) ≤ (53927455852177 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_455 : ∀ t : ℝ, (959611599691 / 2000000000000 : ℝ) < t → t ≤ (240565049861 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-28015414036021488578122489 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (240565049861 / 500000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_456
  have hV : (11024342739165040005921118397839313 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (959611599691 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_455 (Vfield_monotoneOn (show (959611599691 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (959611599691 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_456 : (22081733690044439089963052398915681 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (240565049861 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (240565049861 / 500000000000 : ℝ) := by norm_num
  have hs1 : (69363542277049 / 100000000000000 : ℝ) ≤ Real.sqrt (240565049861 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (240565049861 / 500000000000 : ℝ) ≤ (1387270845541 / 2000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1387270845541 / 2000000000000 : ℝ) = (2000000000000 / 1387270845541 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (69363542277049 / 100000000000000 : ℝ) = (7500000000000 / 69363542277049 : ℝ) := by norm_num
  have hL1 : (39280537728969 / 100000000000000 : ℝ) ≤ Real.log (1 + (240565049861 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((240565049861 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-71999415717801 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (34681771138525 / 110850844277668 : ℝ) ≤ (303220825894259 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1387270845541 / 2000000000000 : ℝ) ≤ (303220825894259 / 500000000000000 : ℝ) := by
    have hw : (15212711069417 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (1387270845541 / 2000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1387270845541 / 2000000000000 : ℝ) / (1 + (15212711069417 / 12500000000000 : ℝ)) = (34681771138525 / 110850844277668 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96435467500637861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2000000000000 / 1387270845541 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2000000000000 / 1387270845541 : ℝ) = (1387270845541 / 2000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 69363542277049 : ℝ) ≤ (13463440274071 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96435467500637861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1387270845541 / 2000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (69363542277049 / 100000000000000 : ℝ)) ≤ (13463440274071 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_456 : ∀ t : ℝ, (240565049861 / 500000000000 : ℝ) < t → t ≤ (19351147979 / 40000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-11147897545662492184428811 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (19351147979 / 40000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_457
  have hV : (22081733690044439089963052398915681 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (240565049861 / 500000000000 : ℝ) := by norm_num
    refine le_trans V_pt_456 (Vfield_monotoneOn (show (240565049861 / 500000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (240565049861 / 500000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_457 : (2214770073238312589791187638926963 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (19351147979 / 40000000000 : ℝ) := by
  have hp : (0 : ℝ) < (19351147979 / 40000000000 : ℝ) := by norm_num
  have hs1 : (6955420184827 / 10000000000000 : ℝ) ≤ Real.sqrt (19351147979 / 40000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (19351147979 / 40000000000 : ℝ) ≤ (69554201848271 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (69554201848271 / 100000000000000 : ℝ) = (100000000000000 / 69554201848271 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (6955420184827 / 10000000000000 : ℝ) = (750000000000 / 6955420184827 : ℝ) := by norm_num
  have hL1 : (7891840185641 / 20000000000000 : ℝ) ≤ Real.log (1 + (19351147979 / 40000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((19351147979 / 40000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-71456756827709 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (9936314549753 / 31687207884963 : ℝ) ≤ (151931940037453 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (69554201848271 / 100000000000000 : ℝ) ≤ (151931940037453 / 250000000000000 : ℝ) := by
    have hw : (121810455194741 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (69554201848271 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (69554201848271 / 100000000000000 : ℝ) / (1 + (121810455194741 / 100000000000000 : ℝ)) = (9936314549753 / 31687207884963 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96306856664508461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 69554201848271 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 69554201848271 : ℝ) = (69554201848271 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 6955420184827 : ℝ) ≤ (107414546896047 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96306856664508461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (69554201848271 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (6955420184827 / 10000000000000 : ℝ)) ≤ (107414546896047 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_457 : ∀ t : ℝ, (19351147979 / 40000000000 : ℝ) < t → t ≤ (121606824807 / 250000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-110903491273259753038719151 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (121606824807 / 250000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_458
  have hV : (2214770073238312589791187638926963 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (19351147979 / 40000000000 : ℝ) := by norm_num
    refine le_trans V_pt_457 (Vfield_monotoneOn (show (19351147979 / 40000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (19351147979 / 40000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_458 : (22213496330801008356994314226791887 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (121606824807 / 250000000000 : ℝ) := by
  have hp : (0 : ℝ) < (121606824807 / 250000000000 : ℝ) := by norm_num
  have hs1 : (69744340216823 / 100000000000000 : ℝ) ≤ Real.sqrt (121606824807 / 250000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (121606824807 / 250000000000 : ℝ) ≤ (8718042527103 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8718042527103 / 12500000000000 : ℝ) = (12500000000000 / 8718042527103 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (69744340216823 / 100000000000000 : ℝ) = (7500000000000 / 69744340216823 : ℝ) := by norm_num
  have hL1 : (7927509098251 / 20000000000000 : ℝ) ≤ Real.log (1 + (121606824807 / 250000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((121606824807 / 250000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-70917026837539 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (17436085054206 / 55479781200289 : ℝ) ≤ (15225201631529 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8718042527103 / 12500000000000 : ℝ) ≤ (15225201631529 / 25000000000000 : ℝ) := by
    have hw : (30479781200289 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (8718042527103 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8718042527103 / 12500000000000 : ℝ) / (1 + (30479781200289 / 25000000000000 : ℝ)) = (17436085054206 / 55479781200289 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96178826153373661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 8718042527103 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 8718042527103 : ℝ) = (8718042527103 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 69744340216823 : ℝ) ≤ (107123949461457 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96178826153373661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8718042527103 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (69744340216823 / 100000000000000 : ℝ)) ≤ (107123949461457 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_458 : ∀ t : ℝ, (121606824807 / 250000000000 : ℝ) < t → t ≤ (489075898981 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-27583721625864756306487941 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (489075898981 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_459
  have hV : (22213496330801008356994314226791887 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (121606824807 / 250000000000 : ℝ) := by norm_num
    refine le_trans V_pt_458 (Vfield_monotoneOn (show (121606824807 / 250000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (121606824807 / 250000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_459 : (22279121748707459142929668254154103 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (489075898981 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (489075898981 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (69933961633887 / 100000000000000 : ℝ) ≤ Real.sqrt (489075898981 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (489075898981 / 1000000000000 : ℝ) ≤ (2185436301059 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2185436301059 / 3125000000000 : ℝ) = (3125000000000 / 2185436301059 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (69933961633887 / 100000000000000 : ℝ) = (2500000000000 / 23311320544629 : ℝ) := by norm_num
  have hL1 : (7963114510527 / 20000000000000 : ℝ) ≤ Real.log (1 + (489075898981 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((489075898981 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-17595048575141 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (8741745204236 / 27753462204227 : ℝ) ≤ (152570654089969 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2185436301059 / 3125000000000 : ℝ) ≤ (152570654089969 / 250000000000000 : ℝ) := by
    have hw : (15253462204227 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (2185436301059 / 3125000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2185436301059 / 3125000000000 : ℝ) / (1 + (15253462204227 / 12500000000000 : ℝ)) = (8741745204236 / 27753462204227 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (96051371043502061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 2185436301059 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 2185436301059 : ℝ) = (2185436301059 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 23311320544629 : ℝ) ≤ (106835697895939 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (96051371043502061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2185436301059 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (69933961633887 / 100000000000000 : ℝ)) ≤ (106835697895939 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_459 : ∀ t : ℝ, (489075898981 / 1000000000000 : ℝ) < t → t ≤ (245862249367 / 500000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-109772874178113316635651493 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (245862249367 / 500000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_460
  have hV : (22279121748707459142929668254154103 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (489075898981 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_459 (Vfield_monotoneOn (show (489075898981 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (489075898981 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_460 : (22344578234174978132674602080597347 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (245862249367 / 500000000000 : ℝ) := by
  have hp : (0 : ℝ) < (245862249367 / 500000000000 : ℝ) := by norm_num
  have hs1 : (70123070293163 / 100000000000000 : ℝ) ≤ Real.sqrt (245862249367 / 500000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (245862249367 / 500000000000 : ℝ) ≤ (17530767573291 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17530767573291 / 25000000000000 : ℝ) = (25000000000000 / 17530767573291 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (70123070293163 / 100000000000000 : ℝ) = (7500000000000 / 70123070293163 : ℝ) := by norm_num
  have hL1 : (39993283240817 / 100000000000000 : ℝ) ≤ Real.log (1 + (245862249367 / 500000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((245862249367 / 500000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-13969245654761 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (23374356764388 / 74045391316933 : ℝ) ≤ (9555491594299 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17530767573291 / 25000000000000 : ℝ) ≤ (9555491594299 / 15625000000000 : ℝ) := by
    have hw : (122136173950799 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (17530767573291 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17530767573291 / 25000000000000 : ℝ) / (1 + (122136173950799 / 100000000000000 : ℝ)) = (23374356764388 / 74045391316933 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (95924486475976061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 17530767573291 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 17530767573291 : ℝ) = (17530767573291 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 70123070293163 : ℝ) ≤ (53274880403021 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (95924486475976061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17530767573291 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (70123070293163 / 100000000000000 : ℝ)) ≤ (53274880403021 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_460 : ∀ t : ℝ, (245862249367 / 500000000000 : ℝ) < t → t ≤ (494373098487 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-109217193148173112841184197 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (494373098487 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_461
  have hV : (22344578234174978132674602080597347 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (245862249367 / 500000000000 : ℝ) := by norm_num
    refine le_trans V_pt_460 (Vfield_monotoneOn (show (245862249367 / 500000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (245862249367 / 500000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_461 : (11204933510099556374371918973752851 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (494373098487 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (494373098487 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (35155835165979 / 50000000000000 : ℝ) ≤ Real.sqrt (494373098487 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (494373098487 / 1000000000000 : ℝ) ≤ (70311670331959 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (70311670331959 / 100000000000000 : ℝ) = (100000000000000 / 70311670331959 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (35155835165979 / 50000000000000 : ℝ) = (1250000000000 / 11718611721993 : ℝ) := by norm_num
  have hL1 : (40170678678263 / 100000000000000 : ℝ) ≤ Real.log (1 + (494373098487 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((494373098487 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-69315098307327 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (10044524333137 / 31749222001292 : ℝ) ≤ (306407325119901 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (70311670331959 / 100000000000000 : ℝ) ≤ (306407325119901 / 500000000000000 : ℝ) := by
    have hw : (30561138502261 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (70311670331959 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (70311670331959 / 100000000000000 : ℝ) / (1 + (30561138502261 / 25000000000000 : ℝ)) = (10044524333137 / 31749222001292 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (95798167655509461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 70311670331959 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 70311670331959 : ℝ) = (70311670331959 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 11718611721993 : ℝ) ≤ (26566526845839 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (95798167655509461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (70311670331959 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (35155835165979 / 50000000000000 : ℝ)) ≤ (26566526845839 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_461 : ∀ t : ℝ, (494373098487 / 1000000000000 : ℝ) < t → t ≤ (1553192807 / 3125000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-54333802283798354885635813 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1553192807 / 3125000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_462
  have hV : (11204933510099556374371918973752851 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (494373098487 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_461 (Vfield_monotoneOn (show (494373098487 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (494373098487 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_462 : (4494997865107035133626694252692743 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (1553192807 / 3125000000 : ℝ) := by
  have hp : (0 : ℝ) < (1553192807 / 3125000000 : ℝ) := by norm_num
  have hs1 : (14099953166447 / 20000000000000 : ℝ) ≤ Real.sqrt (1553192807 / 3125000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1553192807 / 3125000000 : ℝ) ≤ (17624941458059 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17624941458059 / 25000000000000 : ℝ) = (25000000000000 / 17624941458059 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14099953166447 / 20000000000000 : ℝ) = (1500000000000 / 14099953166447 : ℝ) := by norm_num
  have hL1 : (20173879990737 / 50000000000000 : ℝ) ≤ Real.log (1 + (1553192807 / 3125000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1553192807 / 3125000000 : ℝ) + (3 / 40) ^ 2) ≤ (-68786774459819 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (35249882916118 / 111176419032173 : ℝ) ≤ (307036114150991 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17624941458059 / 25000000000000 : ℝ) ≤ (307036114150991 / 500000000000000 : ℝ) := by
    have hw : (61176419032173 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (17624941458059 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17624941458059 / 25000000000000 : ℝ) / (1 + (61176419032173 / 50000000000000 : ℝ)) = (35249882916118 / 111176419032173 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (95672409849291461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 17624941458059 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 17624941458059 : ℝ) = (17624941458059 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 14099953166447 : ℝ) ≤ (6624044211911 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (95672409849291461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17624941458059 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14099953166447 / 20000000000000 : ℝ)) ≤ (6624044211911 / 62500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_462 : ∀ t : ℝ, (1553192807 / 3125000000 : ℝ) < t → t ≤ (499670297993 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-108123888990806898251249589 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (499670297993 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_463
  have hV : (4494997865107035133626694252692743 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1553192807 / 3125000000 : ℝ) := by norm_num
    refine le_trans V_pt_462 (Vfield_monotoneOn (show (1553192807 / 3125000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1553192807 / 3125000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_463 : (22539946352608635464304811087113081 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (499670297993 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (499670297993 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (70687360821649 / 100000000000000 : ℝ) ≤ Real.sqrt (499670297993 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (499670297993 / 1000000000000 : ℝ) ≤ (1413747216433 / 2000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1413747216433 / 2000000000000 : ℝ) = (2000000000000 / 1413747216433 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (70687360821649 / 100000000000000 : ℝ) = (7500000000000 / 70687360821649 : ℝ) := by norm_num
  have hL1 : (4052452826103 / 10000000000000 : ℝ) ≤ Real.log (1 + (499670297993 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((499670297993 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-34130613592231 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (70687360821650 / 222461026371373 : ℝ) ≤ (38457765183521 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1413747216433 / 2000000000000 : ℝ) ≤ (38457765183521 / 62500000000000 : ℝ) := by
    have hw : (122461026371373 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (1413747216433 / 2000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1413747216433 / 2000000000000 : ℝ) / (1 + (122461026371373 / 100000000000000 : ℝ)) = (70687360821650 / 222461026371373 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (95547208385856061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (2000000000000 / 1413747216433 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (2000000000000 / 1413747216433 : ℝ) = (1413747216433 / 2000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 70687360821649 : ℝ) ≤ (105705531147959 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (95547208385856061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1413747216433 / 2000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (70687360821649 / 100000000000000 : ℝ)) ≤ (105705531147959 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_463 : ∀ t : ℝ, (499670297993 / 1000000000000 : ℝ) < t → t ≤ (504967497499 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-53526640981295671411255481 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (504967497499 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_464
  have hV : (22539946352608635464304811087113081 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (499670297993 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_463 (Vfield_monotoneOn (show (499670297993 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (499670297993 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_464 : (22669369316677735184750024109709699 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (504967497499 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (504967497499 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (71061065112971 / 100000000000000 : ℝ) ≤ Real.sqrt (504967497499 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (504967497499 / 1000000000000 : ℝ) ≤ (17765266278243 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17765266278243 / 25000000000000 : ℝ) = (25000000000000 / 17765266278243 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (71061065112971 / 100000000000000 : ℝ) = (7500000000000 / 71061065112971 : ℝ) := by norm_num
  have hL1 : (8175426032429 / 20000000000000 : ℝ) ≤ Real.log (1 + (504967497499 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((504967497499 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-262571667001 / 390625000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (71061065112972 / 222677116753655 : ℝ) ≤ (154452941444727 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17765266278243 / 25000000000000 : ℝ) ≤ (154452941444727 / 250000000000000 : ℝ) := by
    have hw : (24535423350731 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (17765266278243 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17765266278243 / 25000000000000 : ℝ) / (1 + (24535423350731 / 20000000000000 : ℝ)) = (71061065112972 / 222677116753655 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (95298456101598861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 17765266278243 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 17765266278243 : ℝ) = (17765266278243 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 71061065112971 : ℝ) ≤ (105153733903523 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (95298456101598861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17765266278243 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (71061065112971 / 100000000000000 : ℝ)) ≤ (105153733903523 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_464 : ∀ t : ℝ, (504967497499 / 1000000000000 : ℝ) < t → t ≤ (102052939401 / 200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-26500980463338288775446497 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (102052939401 / 200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_465
  have hV : (22669369316677735184750024109709699 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (504967497499 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_464 (Vfield_monotoneOn (show (504967497499 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (504967497499 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_465 : (22798145259346228645619858432901473 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (102052939401 / 200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (102052939401 / 200000000000 : ℝ) := by norm_num
  have hs1 : (71432814378617 / 100000000000000 : ℝ) ≤ Real.sqrt (102052939401 / 200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (102052939401 / 200000000000 : ℝ) ≤ (35716407189309 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (35716407189309 / 50000000000000 : ℝ) = (50000000000000 / 35716407189309 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (71432814378617 / 100000000000000 : ℝ) = (7500000000000 / 71432814378617 : ℝ) := by norm_num
  have hL1 : (1288390410919 / 3125000000000 : ℝ) ≤ Real.log (1 + (102052939401 / 200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((102052939401 / 200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-66186230158591 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (71432814378618 / 222892827170873 : ℝ) ≤ (31013879031439 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (35716407189309 / 50000000000000 : ℝ) ≤ (31013879031439 / 50000000000000 : ℝ) := by
    have hw : (122892827170873 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (35716407189309 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (35716407189309 / 50000000000000 : ℝ) / (1 + (122892827170873 / 100000000000000 : ℝ)) = (71432814378618 / 222892827170873 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (95051874616611661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 35716407189309 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 35716407189309 : ℝ) = (35716407189309 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 71432814378617 : ℝ) ≤ (5107934027 / 48828125000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (95051874616611661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (35716407189309 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (71432814378617 / 100000000000000 : ℝ)) ≤ (5107934027 / 48828125000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_465 : ∀ t : ℝ, (102052939401 / 200000000000 : ℝ) < t → t ≤ (515561896511 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-104974548762107470233148909 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (515561896511 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_466
  have hV : (22798145259346228645619858432901473 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (102052939401 / 200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_465 (Vfield_monotoneOn (show (102052939401 / 200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (102052939401 / 200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_466 : (22926283308781247438304704372212469 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (515561896511 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (515561896511 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (71802638984301 / 100000000000000 : ℝ) ≤ Real.sqrt (515561896511 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (515561896511 / 1000000000000 : ℝ) ≤ (35901319492151 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (35901319492151 / 50000000000000 : ℝ) = (50000000000000 / 35901319492151 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (71802638984301 / 100000000000000 : ℝ) = (2500000000000 / 23934212994767 : ℝ) := by norm_num
  have hL1 : (20789312949261 / 50000000000000 : ℝ) ≤ Real.log (1 + (515561896511 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((515561896511 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-13032931495743 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (71802638984302 / 223108159620351 : ℝ) ≤ (62272204021221 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (35901319492151 / 50000000000000 : ℝ) ≤ (62272204021221 / 100000000000000 : ℝ) := by
    have hw : (123108159620351 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (35901319492151 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (35901319492151 / 50000000000000 : ℝ) / (1 + (123108159620351 / 100000000000000 : ℝ)) = (71802638984302 / 223108159620351 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94807428658268661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 35901319492151 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 35901319492151 : ℝ) = (35901319492151 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 23934212994767 : ℝ) ≤ (104075577396717 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94807428658268661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (35901319492151 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (71802638984301 / 100000000000000 : ℝ)) ≤ (104075577396717 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_466 : ∀ t : ℝ, (515561896511 / 1000000000000 : ℝ) < t → t ≤ (16577867570387 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-20703521318119147200439787 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (16577867570387 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_467
  have hV : (22926283308781247438304704372212469 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (515561896511 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_466 (Vfield_monotoneOn (show (515561896511 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (515561896511 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_467 : (4597290726317550899797328728137343 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (16577867570387 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (16577867570387 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (14395254239847 / 20000000000000 : ℝ) ≤ Real.sqrt (16577867570387 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (16577867570387 / 32000000000000 : ℝ) ≤ (17994067799809 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17994067799809 / 25000000000000 : ℝ) = (25000000000000 / 17994067799809 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14395254239847 / 20000000000000 : ℝ) = (500000000000 / 4798418079949 : ℝ) := by norm_num
  have hL1 : (41743212459447 / 100000000000000 : ℝ) ≤ Real.log (1 + (16577867570387 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((16577867570387 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-32343402442557 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (17994067799809 / 55802377765103 : ℝ) ≤ (311933380180461 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17994067799809 / 25000000000000 : ℝ) ≤ (311933380180461 / 500000000000000 : ℝ) := by
    have hw : (30802377765103 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (17994067799809 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17994067799809 / 25000000000000 : ℝ) / (1 + (30802377765103 / 25000000000000 : ℝ)) = (17994067799809 / 55802377765103 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94692956643397461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 17994067799809 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 17994067799809 : ℝ) = (17994067799809 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4798418079949 : ℝ) ≤ (103826312890931 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94692956643397461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17994067799809 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14395254239847 / 20000000000000 : ℝ)) ≤ (103826312890931 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_467 : ∀ t : ℝ, (16577867570387 / 32000000000000 : ℝ) < t → t ≤ (8328877226211 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-102639010026893740582757019 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8328877226211 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_468
  have hV : (4597290726317550899797328728137343 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (16577867570387 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_467 (Vfield_monotoneOn (show (16577867570387 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (16577867570387 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_468 : (23046485176093609922488708600867613 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (8328877226211 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8328877226211 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (72149485558677 / 100000000000000 : ℝ) ≤ Real.sqrt (8328877226211 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8328877226211 / 16000000000000 : ℝ) ≤ (36074742779339 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (36074742779339 / 50000000000000 : ℝ) = (50000000000000 / 36074742779339 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (72149485558677 / 100000000000000 : ℝ) = (2500000000000 / 24049828519559 : ℝ) := by norm_num
  have hL1 : (41907528578061 / 100000000000000 : ℝ) ≤ Real.log (1 + (8328877226211 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8328877226211 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-64211224867267 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (72149485558678 / 223310779197853 : ℝ) ≤ (312503424620791 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (36074742779339 / 50000000000000 : ℝ) ≤ (312503424620791 / 500000000000000 : ℝ) := by
    have hw : (123310779197853 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (36074742779339 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (36074742779339 / 50000000000000 : ℝ) / (1 + (123310779197853 / 100000000000000 : ℝ)) = (72149485558678 / 223310779197853 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94578947755331461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 36074742779339 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 36074742779339 : ℝ) = (36074742779339 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 24049828519559 : ℝ) ≤ (51789415428873 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94578947755331461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (36074742779339 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (72149485558677 / 100000000000000 : ℝ)) ≤ (51789415428873 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_468 : ∀ t : ℝ, (8328877226211 / 16000000000000 : ℝ) < t → t ≤ (16737641334457 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-101859189396655685586753089 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (16737641334457 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_469
  have hV : (23046485176093609922488708600867613 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8328877226211 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_468 (Vfield_monotoneOn (show (8328877226211 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8328877226211 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_469 : (23106378849883619660739610306311547 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (16737641334457 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (16737641334457 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (72322285064963 / 100000000000000 : ℝ) ≤ Real.sqrt (16737641334457 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (16737641334457 / 32000000000000 : ℝ) ≤ (18080571266241 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18080571266241 / 25000000000000 : ℝ) = (25000000000000 / 18080571266241 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (72322285064963 / 100000000000000 : ℝ) = (7500000000000 / 72322285064963 : ℝ) := by norm_num
  have hL1 : (4207157514167 / 10000000000000 : ℝ) ≤ Real.log (1 + (16737641334457 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((16737641334457 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2549515836463 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (12053714177494 / 37235327372957 : ℝ) ≤ (313071170888963 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18080571266241 / 25000000000000 : ℝ) ≤ (313071170888963 / 500000000000000 : ℝ) := by
    have hw : (61705982118871 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (18080571266241 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (18080571266241 / 25000000000000 : ℝ) / (1 + (61705982118871 / 50000000000000 : ℝ)) = (12053714177494 / 37235327372957 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94465398501697061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 18080571266241 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 18080571266241 : ℝ) = (18080571266241 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 72322285064963 : ℝ) ≤ (103333110153833 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94465398501697061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18080571266241 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (72322285064963 / 100000000000000 : ℝ)) ≤ (103333110153833 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_469 : ∀ t : ℝ, (16737641334457 / 32000000000000 : ℝ) < t → t ≤ (33555169550949 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-50745297258182312059113269 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (33555169550949 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_470
  have hV : (23106378849883619660739610306311547 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (16737641334457 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_469 (Vfield_monotoneOn (show (16737641334457 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (16737641334457 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_470 : (23136274266202743478558810897791169 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (33555169550949 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (33555169550949 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (72408530176601 / 100000000000000 : ℝ) ≤ Real.sqrt (33555169550949 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (33555169550949 / 64000000000000 : ℝ) ≤ (36204265088301 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (36204265088301 / 50000000000000 : ℝ) = (50000000000000 / 36204265088301 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (72408530176601 / 100000000000000 : ℝ) = (7500000000000 / 72408530176601 : ℝ) := by norm_num
  have hL1 : (8430699523287 / 20000000000000 : ℝ) ≤ Real.log (1 + (33555169550949 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((33555169550949 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-63502068942333 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (36204265088301 / 111731262829979 : ℝ) ≤ (156677093804837 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (36204265088301 / 50000000000000 : ℝ) ≤ (156677093804837 / 250000000000000 : ℝ) := by
    have hw : (61731262829979 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (36204265088301 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (36204265088301 / 50000000000000 : ℝ) / (1 + (61731262829979 / 50000000000000 : ℝ)) = (36204265088301 / 111731262829979 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94408795157554861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 36204265088301 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 36204265088301 : ℝ) = (36204265088301 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 72408530176601 : ℝ) ≤ (51605451894411 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94408795157554861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (36204265088301 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (72408530176601 / 100000000000000 : ℝ)) ≤ (51605451894411 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_470 : ∀ t : ℝ, (33555169550949 / 64000000000000 : ℝ) < t → t ≤ (4204382054123 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-101132443962004193422752841 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4204382054123 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_471
  have hV : (23136274266202743478558810897791169 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (33555169550949 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_470 (Vfield_monotoneOn (show (33555169550949 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (33555169550949 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_471 : (5791533887691261030629325518207809 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (4204382054123 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4204382054123 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (18123668171161 / 25000000000000 : ℝ) ≤ Real.sqrt (4204382054123 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4204382054123 / 8000000000000 : ℝ) ≤ (14498934536929 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (14498934536929 / 20000000000000 : ℝ) = (20000000000000 / 14498934536929 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (18123668171161 / 25000000000000 : ℝ) = (1875000000000 / 18123668171161 : ℝ) := by norm_num
  have hL1 : (8447070606643 / 20000000000000 : ℝ) ≤ Real.log (1 + (4204382054123 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4204382054123 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-63266796808491 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (14498934536929 / 44702613276861 : ℝ) ≤ (313636636243663 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (14498934536929 / 20000000000000 : ℝ) ≤ (313636636243663 / 500000000000000 : ℝ) := by
    have hw : (24702613276861 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (14498934536929 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (14498934536929 / 20000000000000 : ℝ) / (1 + (24702613276861 / 20000000000000 : ℝ)) = (14498934536929 / 44702613276861 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94352305430757061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 14498934536929 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 14498934536929 : ℝ) = (14498934536929 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 18123668171161 : ℝ) ≤ (25772282496331 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94352305430757061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (14498934536929 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (18123668171161 / 25000000000000 : ℝ)) ≤ (25772282496331 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_471 : ∀ t : ℝ, (4204382054123 / 8000000000000 : ℝ) < t → t ≤ (33714943315019 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-50391501051135338792786361 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (33714943315019 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_472
  have hV : (5791533887691261030629325518207809 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4204382054123 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_471 (Vfield_monotoneOn (show (4204382054123 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4204382054123 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_472 : (11597981407146476357918607129238721 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (33714943315019 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (33714943315019 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (36290356477209 / 50000000000000 : ℝ) ≤ Real.sqrt (33714943315019 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (33714943315019 / 64000000000000 : ℝ) ≤ (72580712954419 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (72580712954419 / 100000000000000 : ℝ) = (100000000000000 / 72580712954419 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (36290356477209 / 50000000000000 : ℝ) = (1250000000000 / 12096785492403 : ℝ) := by norm_num
  have hL1 : (21158570750849 / 50000000000000 : ℝ) ≤ Real.log (1 + (33714943315019 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((33714943315019 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-63032076905427 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (72580712954419 / 223563586436181 : ℝ) ≤ (313918518917059 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (72580712954419 / 100000000000000 : ℝ) ≤ (313918518917059 / 500000000000000 : ℝ) := by
    have hw : (123563586436181 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (72580712954419 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (72580712954419 / 100000000000000 : ℝ) / (1 + (123563586436181 / 100000000000000 : ℝ)) = (72580712954419 / 223563586436181 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94295928896077861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 72580712954419 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 72580712954419 : ℝ) = (72580712954419 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 12096785492403 : ℝ) ≤ (12870973274687 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94295928896077861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (72580712954419 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (36290356477209 / 50000000000000 : ℝ)) ≤ (12870973274687 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_472 : ∀ t : ℝ, (33714943315019 / 64000000000000 : ℝ) < t → t ≤ (16897415098527 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-100441001919256727840964297 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (16897415098527 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_473
  have hV : (11597981407146476357918607129238721 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (33714943315019 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_472 (Vfield_monotoneOn (show (33714943315019 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (33714943315019 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_473 : (11612878083458171858699361976378567 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (16897415098527 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (16897415098527 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (36333325674543 / 50000000000000 : ℝ) ≤ Real.sqrt (16897415098527 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (16897415098527 / 32000000000000 : ℝ) ≤ (72666651349087 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (72666651349087 / 100000000000000 : ℝ) = (100000000000000 / 72666651349087 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (36333325674543 / 50000000000000 : ℝ) = (1250000000000 / 12111108558181 : ℝ) := by norm_num
  have hL1 : (42398863131309 / 100000000000000 : ℝ) ≤ Real.log (1 + (16897415098527 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((16897415098527 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-62797906646819 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (72666651349087 / 223614085840933 : ℝ) ≤ (157099918871849 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (72666651349087 / 100000000000000 : ℝ) ≤ (157099918871849 / 250000000000000 : ℝ) := by
    have hw : (123614085840933 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (72666651349087 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (72666651349087 / 100000000000000 : ℝ) / (1 + (123614085840933 / 100000000000000 : ℝ)) = (72666651349087 / 223614085840933 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94239665130750061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 72666651349087 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 72666651349087 : ℝ) = (72666651349087 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 12111108558181 : ℝ) ≤ (102846869900423 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94239665130750061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (72666651349087 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (36333325674543 / 50000000000000 : ℝ)) ≤ (102846869900423 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_473 : ∀ t : ℝ, (16897415098527 / 32000000000000 : ℝ) < t → t ≤ (33874717079089 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-50052742044403034726323263 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (33874717079089 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_474
  have hV : (11612878083458171858699361976378567 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (16897415098527 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_473 (Vfield_monotoneOn (show (16897415098527 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (16897415098527 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_474 : (4651103143635217471882276811927477 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (33874717079089 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (33874717079089 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (14550497645933 / 20000000000000 : ℝ) ≤ Real.sqrt (33874717079089 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (33874717079089 / 64000000000000 : ℝ) ≤ (36376244114833 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (36376244114833 / 50000000000000 : ℝ) = (50000000000000 / 36376244114833 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14550497645933 / 20000000000000 : ℝ) = (1500000000000 / 14550497645933 : ℝ) := by norm_num
  have hL1 : (42480518031201 / 100000000000000 : ℝ) ≤ Real.log (1 + (33874717079089 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((33874717079089 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6256428346447 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (72752488229666 / 223664564623855 : ℝ) ≤ (314480594825219 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (36376244114833 / 50000000000000 : ℝ) ≤ (314480594825219 / 500000000000000 : ℝ) := by
    have hw : (24732912924771 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (36376244114833 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (36376244114833 / 50000000000000 : ℝ) / (1 + (24732912924771 / 20000000000000 : ℝ)) = (72752488229666 / 223664564623855 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94183513714445861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 36376244114833 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 36376244114833 : ℝ) = (36376244114833 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 14550497645933 : ℝ) ≤ (51363189294949 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94183513714445861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (36376244114833 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14550497645933 / 20000000000000 : ℝ)) ≤ (51363189294949 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_474 : ∀ t : ℝ, (33874717079089 / 64000000000000 : ℝ) < t → t ≤ (8488650990281 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-99775700861920154147546323 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8488650990281 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_475
  have hV : (4651103143635217471882276811927477 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (33874717079089 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_474 (Vfield_monotoneOn (show (33874717079089 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (33874717079089 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_475 : (23285241577029789384845774769126143 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (8488650990281 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8488650990281 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (72838223955047 / 100000000000000 : ℝ) ≤ Real.sqrt (8488650990281 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8488650990281 / 16000000000000 : ℝ) ≤ (9104777994381 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9104777994381 / 12500000000000 : ℝ) = (12500000000000 / 9104777994381 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (72838223955047 / 100000000000000 : ℝ) = (7500000000000 / 72838223955047 : ℝ) := by norm_num
  have hL1 : (42562106310261 / 100000000000000 : ℝ) ≤ Real.log (1 + (8488650990281 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8488650990281 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-62331204808143 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (24279407985016 / 74571674270063 : ℝ) ≤ (12590431690047 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9104777994381 / 12500000000000 : ℝ) ≤ (12590431690047 / 20000000000000 : ℝ) := by
    have hw : (123715022810189 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (9104777994381 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (9104777994381 / 12500000000000 : ℝ) / (1 + (123715022810189 / 100000000000000 : ℝ)) = (24279407985016 / 74571674270063 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94127474229254661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 9104777994381 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 9104777994381 : ℝ) = (9104777994381 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 72838223955047 : ℝ) ≤ (102606309782203 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94127474229254661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9104777994381 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (72838223955047 / 100000000000000 : ℝ)) ≤ (102606309782203 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_475 : ∀ t : ℝ, (8488650990281 / 16000000000000 : ℝ) < t → t ≤ (34034490843159 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-9945105544537358776283173 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (34034490843159 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_476
  have hV : (23285241577029789384845774769126143 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8488650990281 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_475 (Vfield_monotoneOn (show (8488650990281 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8488650990281 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_476 : (23314933851854467073802650464501459 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (34034490843159 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (34034490843159 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (72923858882011 / 100000000000000 : ℝ) ≤ Real.sqrt (34034490843159 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (34034490843159 / 64000000000000 : ℝ) ≤ (18230964720503 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18230964720503 / 25000000000000 : ℝ) = (25000000000000 / 18230964720503 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (72923858882011 / 100000000000000 : ℝ) = (7500000000000 / 72923858882011 : ℝ) := by norm_num
  have hL1 : (5330453509639 / 12500000000000 : ℝ) ≤ Real.log (1 + (34034490843159 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((34034490843159 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6209866814539 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (36461929441006 / 111882730212563 : ℝ) ≤ (63008086419821 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18230964720503 / 25000000000000 : ℝ) ≤ (63008086419821 / 100000000000000 : ℝ) := by
    have hw : (61882730212563 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (18230964720503 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (18230964720503 / 25000000000000 : ℝ) / (1 + (61882730212563 / 50000000000000 : ℝ)) = (36461929441006 / 111882730212563 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94071546259668661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 18230964720503 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 18230964720503 : ℝ) = (18230964720503 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 72923858882011 : ℝ) ≤ (12810832626737 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94071546259668661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18230964720503 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (72923858882011 / 100000000000000 : ℝ)) ≤ (12810832626737 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_476 : ∀ t : ℝ, (34034490843159 / 64000000000000 : ℝ) < t → t ≤ (17057188862597 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-99131062059749066467410981 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (17057188862597 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_477
  have hV : (23314933851854467073802650464501459 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (34034490843159 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_476 (Vfield_monotoneOn (show (34034490843159 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (34034490843159 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_477 : (91189815040832262797313903343577 / 19531250000000000000000000000000 : ℝ) ≤ Vfield (17057188862597 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (17057188862597 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (285192942833 / 390625000000 : ℝ) ≤ Real.sqrt (17057188862597 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (17057188862597 / 32000000000000 : ℝ) ≤ (73009393365249 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (73009393365249 / 100000000000000 : ℝ) = (100000000000000 / 73009393365249 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (285192942833 / 390625000000 : ℝ) = (29296875000 / 285192942833 : ℝ) := by norm_num
  have hL1 : (42725083440107 / 100000000000000 : ℝ) ≤ Real.log (1 + (17057188862597 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((17057188862597 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-61866670961389 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73009393365249 / 223815877493807 : ℝ) ≤ (315319516434661 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (73009393365249 / 100000000000000 : ℝ) ≤ (315319516434661 / 500000000000000 : ℝ) := by
    have hw : (123815877493807 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (73009393365249 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (73009393365249 / 100000000000000 : ℝ) / (1 + (123815877493807 / 100000000000000 : ℝ)) = (73009393365249 / 223815877493807 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (94015729392557461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 73009393365249 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 73009393365249 : ℝ) = (73009393365249 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (29296875000 / 285192942833 : ℝ) ≤ (12795928730199 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (94015729392557461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (73009393365249 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (285192942833 / 390625000000 : ℝ)) ≤ (12795928730199 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_477 : ∀ t : ℝ, (17057188862597 / 32000000000000 : ℝ) < t → t ≤ (34194264607229 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-98815318657038198641029013 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (34194264607229 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_478
  have hV : (91189815040832262797313903343577 / 19531250000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (17057188862597 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_477 (Vfield_monotoneOn (show (17057188862597 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (17057188862597 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_478 : (23374218080055931503224065228881761 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (34194264607229 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (34194264607229 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (73094827757369 / 100000000000000 : ℝ) ≤ Real.sqrt (34194264607229 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (34194264607229 / 64000000000000 : ℝ) ≤ (7309482775737 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7309482775737 / 10000000000000 : ℝ) = (10000000000000 / 7309482775737 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73094827757369 / 100000000000000 : ℝ) = (7500000000000 / 73094827757369 : ℝ) := by norm_num
  have hL1 : (42806472507339 / 100000000000000 : ℝ) ≤ Real.log (1 + (34194264607229 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((34194264607229 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3081760537939 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7309482775737 / 22386627404132 : ℝ) ≤ (315598047311667 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7309482775737 / 10000000000000 : ℝ) ≤ (315598047311667 / 500000000000000 : ℝ) := by
    have hw : (3096656851033 / 2500000000000 : ℝ) ≤ Real.sqrt (1 + (7309482775737 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7309482775737 / 10000000000000 : ℝ) / (1 + (3096656851033 / 2500000000000 : ℝ)) = (7309482775737 / 22386627404132 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93960023217156261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 7309482775737 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 7309482775737 : ℝ) = (7309482775737 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 73094827757369 : ℝ) ≤ (51124306920883 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93960023217156261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7309482775737 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73094827757369 / 100000000000000 : ℝ)) ≤ (51124306920883 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_478 : ∀ t : ℝ, (34194264607229 / 64000000000000 : ℝ) < t → t ≤ (68468416096493 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-12332366638326371701365347 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (68468416096493 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_479
  have hV : (23374218080055931503224065228881761 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (34194264607229 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_478 (Vfield_monotoneOn (show (34194264607229 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (34194264607229 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_479 : (2338901831483877784646905921036641 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (68468416096493 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (68468416096493 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (7313750752889 / 10000000000000 : ℝ) ≤ Real.sqrt (68468416096493 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (68468416096493 / 128000000000000 : ℝ) ≤ (73137507528891 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (73137507528891 / 100000000000000 : ℝ) = (100000000000000 / 73137507528891 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7313750752889 / 10000000000000 : ℝ) = (750000000000 / 7313750752889 : ℝ) := by norm_num
  have hL1 : (34277713771 / 80000000000 : ℝ) ≤ Real.log (1 + (68468416096493 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((68468416096493 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3844980078113 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (24379169176297 / 74630488209155 : ℝ) ≤ (157868552920917 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (73137507528891 / 100000000000000 : ℝ) ≤ (157868552920917 / 250000000000000 : ℝ) := by
    have hw : (24778292925493 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (73137507528891 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (73137507528891 / 100000000000000 : ℝ) / (1 + (24778292925493 / 20000000000000 : ℝ)) = (24379169176297 / 74630488209155 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93932211511122861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 73137507528891 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 73137507528891 : ℝ) = (73137507528891 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 7313750752889 : ℝ) ≤ (25547340194889 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93932211511122861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (73137507528891 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7313750752889 / 10000000000000 : ℝ)) ≤ (25547340194889 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_479 : ∀ t : ℝ, (68468416096493 / 128000000000000 : ℝ) < t → t ≤ (2142134468079 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-98503487703236182990243681 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2142134468079 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_480
  have hV : (2338901831483877784646905921036641 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (68468416096493 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_479 (Vfield_monotoneOn (show (68468416096493 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (68468416096493 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
