import Apery.Table2.U12
import Apery.Table2.U13

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_480 : (2340381024732767896836761511651717 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (2142134468079 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2142134468079 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (7318016240893 / 10000000000000 : ℝ) ≤ Real.sqrt (2142134468079 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2142134468079 / 4000000000000 : ℝ) ≤ (73180162408931 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (73180162408931 / 100000000000000 : ℝ) = (100000000000000 / 73180162408931 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (7318016240893 / 10000000000000 : ℝ) = (750000000000 / 7318016240893 : ℝ) := by norm_num
  have hL1 : (21443897693317 / 50000000000000 : ℝ) ≤ Real.log (1 + (2142134468079 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2142134468079 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-30702142528753 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73180162408931 / 223916650092703 : ℝ) ≤ (157938013386123 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (73180162408931 / 100000000000000 : ℝ) ≤ (157938013386123 / 250000000000000 : ℝ) := by
    have hw : (123916650092703 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (73180162408931 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (73180162408931 / 100000000000000 : ℝ) / (1 + (123916650092703 / 100000000000000 : ℝ)) = (73180162408931 / 223916650092703 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93904427325040461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 73180162408931 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 73180162408931 : ℝ) = (73180162408931 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 7318016240893 : ℝ) ≤ (25532552652633 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93904427325040461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (73180162408931 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (7318016240893 / 10000000000000 : ℝ)) ≤ (25532552652633 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_480 : ∀ t : ℝ, (2142134468079 / 4000000000000 : ℝ) < t → t ≤ (68628189860563 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-98348948063914334337106549 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (68628189860563 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_481
  have hV : (2340381024732767896836761511651717 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2142134468079 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_480 (Vfield_monotoneOn (show (2142134468079 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2142134468079 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_481 : (23418593890768222906460475320457079 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (68628189860563 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (68628189860563 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (73222792440991 / 100000000000000 : ℝ) ≤ Real.sqrt (68628189860563 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (68628189860563 / 128000000000000 : ℝ) ≤ (2288212263781 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2288212263781 / 3125000000000 : ℝ) = (3125000000000 / 2288212263781 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73222792440991 / 100000000000000 : ℝ) = (7500000000000 / 73222792440991 : ℝ) := by norm_num
  have hL1 : (4292843203943 / 10000000000000 : ℝ) ≤ Real.log (1 + (68628189860563 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((68628189860563 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-30644510937271 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (18305698110248 / 55985457610039 : ℝ) ≤ (316014810356359 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2288212263781 / 3125000000000 : ℝ) ≤ (316014810356359 / 500000000000000 : ℝ) := by
    have hw : (30985457610039 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (2288212263781 / 3125000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2288212263781 / 3125000000000 : ℝ) / (1 + (30985457610039 / 25000000000000 : ℝ)) = (18305698110248 / 55985457610039 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93876670608217861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 2288212263781 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 2288212263781 : ℝ) = (2288212263781 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 73222792440991 : ℝ) ≤ (20414232607449 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93876670608217861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2288212263781 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73222792440991 / 100000000000000 : ℝ)) ≤ (20414232607449 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_481 : ∀ t : ℝ, (68628189860563 / 128000000000000 : ℝ) < t → t ≤ (34354038371299 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-24548820577656845116320693 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (34354038371299 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_482
  have hV : (23418593890768222906460475320457079 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (68628189860563 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_481 (Vfield_monotoneOn (show (68628189860563 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (68628189860563 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_482 : (4686673851673991161960904887271841 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (34354038371299 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (34354038371299 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (14653079533689 / 20000000000000 : ℝ) ≤ Real.sqrt (34354038371299 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (34354038371299 / 64000000000000 : ℝ) ≤ (36632698834223 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (36632698834223 / 50000000000000 : ℝ) = (50000000000000 / 36632698834223 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14653079533689 / 20000000000000 : ℝ) = (500000000000 / 4884359844563 : ℝ) := by norm_num
  have hL1 : (42969052185557 / 100000000000000 : ℝ) ≤ Real.log (1 + (34354038371299 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((34354038371299 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7646736424331 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73265397668446 / 223967005672943 : ℝ) ≤ (158076728423447 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (36632698834223 / 50000000000000 : ℝ) ≤ (158076728423447 / 250000000000000 : ℝ) := by
    have hw : (123967005672943 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (36632698834223 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (36632698834223 / 50000000000000 : ℝ) / (1 + (123967005672943 / 100000000000000 : ℝ)) = (73265397668446 / 223967005672943 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93848941310110861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 36632698834223 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 36632698834223 : ℝ) = (36632698834223 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4884359844563 : ℝ) ≤ (102012217763449 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93848941310110861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (36632698834223 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14653079533689 / 20000000000000 : ℝ)) ≤ (102012217763449 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_482 : ∀ t : ℝ, (34354038371299 / 64000000000000 : ℝ) < t → t ≤ (68787963624633 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-19608492163113863411508397 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (68787963624633 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_483
  have hV : (4686673851673991161960904887271841 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (34354038371299 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_482 (Vfield_monotoneOn (show (34354038371299 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (34354038371299 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_483 : (23448136363308804947717899607347029 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (68787963624633 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (68787963624633 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (73307978134541 / 100000000000000 : ℝ) ≤ Real.sqrt (68787963624633 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (68787963624633 / 128000000000000 : ℝ) ≤ (36653989067271 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (36653989067271 / 50000000000000 : ℝ) = (50000000000000 / 36653989067271 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73307978134541 / 100000000000000 : ℝ) = (7500000000000 / 73307978134541 : ℝ) := by norm_num
  have hL1 : (21504827919211 / 50000000000000 : ℝ) ≤ Real.log (1 + (68787963624633 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((68787963624633 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-61058893312613 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (36653989067271 / 111996087897089 : ℝ) ≤ (158145983247933 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (36653989067271 / 50000000000000 : ℝ) ≤ (158145983247933 / 250000000000000 : ℝ) := by
    have hw : (61996087897089 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (36653989067271 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (36653989067271 / 50000000000000 : ℝ) / (1 + (61996087897089 / 50000000000000 : ℝ)) = (36653989067271 / 111996087897089 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93821239380316461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 36653989067271 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 36653989067271 : ℝ) = (36653989067271 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 73307978134541 : ℝ) ≤ (101953374494093 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93821239380316461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (36653989067271 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73307978134541 / 100000000000000 : ℝ)) ≤ (101953374494093 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_483 : ∀ t : ℝ, (68787963624633 / 128000000000000 : ℝ) < t → t ≤ (17216962626667 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-19578091195774698314443771 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (17216962626667 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_484
  have hV : (23448136363308804947717899607347029 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (68787963624633 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_483 (Vfield_monotoneOn (show (68787963624633 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (68787963624633 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_484 : (11731447609362841397144157005168569 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (17216962626667 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (17216962626667 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (36675266941201 / 50000000000000 : ℝ) ≤ Real.sqrt (17216962626667 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (17216962626667 / 32000000000000 : ℝ) ≤ (73350533882403 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (73350533882403 / 100000000000000 : ℝ) = (100000000000000 / 73350533882403 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (36675266941201 / 50000000000000 : ℝ) = (3750000000000 / 36675266941201 : ℝ) := by norm_num
  have hL1 : (43050243011411 / 100000000000000 : ℝ) ≤ Real.log (1 + (17216962626667 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((17216962626667 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15236006831069 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73350533882403 / 224017340806975 : ℝ) ≤ (316430339554573 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (73350533882403 / 100000000000000 : ℝ) ≤ (316430339554573 / 500000000000000 : ℝ) := by
    have hw : (4960693632279 / 4000000000000 : ℝ) ≤ Real.sqrt (1 + (73350533882403 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (73350533882403 / 100000000000000 : ℝ) / (1 + (4960693632279 / 4000000000000 : ℝ)) = (73350533882403 / 224017340806975 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93793564768575061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 73350533882403 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 73350533882403 : ℝ) = (73350533882403 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 36675266941201 : ℝ) ≤ (20378926587063 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93793564768575061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (73350533882403 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (36675266941201 / 50000000000000 : ℝ)) ≤ (20378926587063 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_484 : ∀ t : ℝ, (17216962626667 / 32000000000000 : ℝ) < t → t ≤ (68947737388703 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-97739242033910878275645023 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (68947737388703 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_485
  have hV : (11731447609362841397144157005168569 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (17216962626667 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_484 (Vfield_monotoneOn (show (17216962626667 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (17216962626667 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_485 : (1467352864857902546188623980865841 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (68947737388703 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (68947737388703 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (4587066559689 / 6250000000000 : ℝ) ≤ Real.sqrt (68947737388703 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (68947737388703 / 128000000000000 : ℝ) ≤ (2935722598201 / 4000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2935722598201 / 4000000000000 : ℝ) = (4000000000000 / 2935722598201 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4587066559689 / 6250000000000 : ℝ) = (156250000000 / 1529022186563 : ℝ) := by norm_num
  have hL1 : (43090813717897 / 100000000000000 : ℝ) ≤ Real.log (1 + (68947737388703 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((68947737388703 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-15207323281631 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73393064955025 / 224042500714442 : ℝ) ≤ (158284288136797 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2935722598201 / 4000000000000 : ℝ) ≤ (158284288136797 / 250000000000000 : ℝ) := by
    have hw : (62021250357221 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (2935722598201 / 4000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2935722598201 / 4000000000000 : ℝ) / (1 + (62021250357221 / 50000000000000 : ℝ)) = (73393064955025 / 224042500714442 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93765917424770861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (4000000000000 / 2935722598201 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (4000000000000 / 2935722598201 : ℝ) = (2935722598201 / 4000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (156250000000 / 1529022186563 : ℝ) ≤ (2545899819861 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93765917424770861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2935722598201 / 4000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4587066559689 / 6250000000000 : ℝ)) ≤ (2545899819861 / 25000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_485 : ∀ t : ℝ, (68947737388703 / 128000000000000 : ℝ) < t → t ≤ (34513812135369 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-12198599359510663609427039 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (34513812135369 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_486
  have hV : (1467352864857902546188623980865841 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (68947737388703 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_485 (Vfield_monotoneOn (show (68947737388703 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (68947737388703 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_486 : (293654852917287584469821600422129 / 62500000000000000000000000000000 : ℝ) ≤ Vfield (34513812135369 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (34513812135369 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (917944642441 / 1250000000000 : ℝ) ≤ Real.sqrt (34513812135369 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (34513812135369 / 64000000000000 : ℝ) ≤ (73435571395281 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (73435571395281 / 100000000000000 : ℝ) = (100000000000000 / 73435571395281 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (917944642441 / 1250000000000 : ℝ) = (93750000000 / 917944642441 : ℝ) := by norm_num
  have hL1 : (10782841992809 / 25000000000000 : ℝ) ≤ Real.log (1 + (34513812135369 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((34513812135369 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-12142938083457 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73435571395281 / 224067655519685 : ℝ) ≤ (316706676902803 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (73435571395281 / 100000000000000 : ℝ) ≤ (316706676902803 / 500000000000000 : ℝ) := by
    have hw : (24813531103937 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (73435571395281 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (73435571395281 / 100000000000000 : ℝ) / (1 + (24813531103937 / 20000000000000 : ℝ)) = (73435571395281 / 224067655519685 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93738297298929061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 73435571395281 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 73435571395281 : ℝ) = (73435571395281 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (93750000000 / 917944642441 : ℝ) ≤ (101777453779969 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93738297298929061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (73435571395281 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (917944642441 / 1250000000000 : ℝ)) ≤ (101777453779969 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_486 : ∀ t : ℝ, (34513812135369 / 64000000000000 : ℝ) < t → t ≤ (69107511152773 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-97439091911747864533891967 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (69107511152773 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_487
  have hV : (293654852917287584469821600422129 / 62500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (34513812135369 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_486 (Vfield_monotoneOn (show (34513812135369 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (34513812135369 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_487 : (146919515117083785445408938608203 / 31250000000000000000000000000000 : ℝ) ≤ Vfield (69107511152773 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (69107511152773 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (459237832787 / 625000000000 : ℝ) ≤ Real.sqrt (69107511152773 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (69107511152773 / 128000000000000 : ℝ) ≤ (73478053245921 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (73478053245921 / 100000000000000 : ℝ) = (100000000000000 / 73478053245921 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (459237832787 / 625000000000 : ℝ) = (46875000000 / 459237832787 : ℝ) := by norm_num
  have hL1 : (43171905784767 / 100000000000000 : ℝ) ≤ Real.log (1 + (69107511152773 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((69107511152773 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-30300109447763 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (24492684415307 / 74697601741936 : ℝ) ≤ (316844641691371 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (73478053245921 / 100000000000000 : ℝ) ≤ (316844641691371 / 500000000000000 : ℝ) := by
    have hw : (7755800326613 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (73478053245921 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (73478053245921 / 100000000000000 : ℝ) / (1 + (7755800326613 / 6250000000000 : ℝ)) = (24492684415307 / 74697601741936 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93710704341215461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 73478053245921 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 73478053245921 : ℝ) = (73478053245921 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (46875000000 / 459237832787 : ℝ) ≤ (101719015601573 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93710704341215461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (73478053245921 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (459237832787 / 625000000000 : ℝ)) ≤ (101719015601573 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_487 : ∀ t : ℝ, (69107511152773 / 128000000000000 : ℝ) < t → t ≤ (8648424754351 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-19458022384882365165860177 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8648424754351 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_488
  have hV : (146919515117083785445408938608203 / 31250000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (69107511152773 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_487 (Vfield_monotoneOn (show (69107511152773 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (69107511152773 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_488 : (23521848406780898977880614933283561 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (8648424754351 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8648424754351 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (73520510549569 / 100000000000000 : ℝ) ≤ Real.sqrt (8648424754351 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8648424754351 / 16000000000000 : ℝ) ≤ (7352051054957 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7352051054957 / 10000000000000 : ℝ) = (10000000000000 / 7352051054957 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73520510549569 / 100000000000000 : ℝ) = (7500000000000 / 73520510549569 : ℝ) := by norm_num
  have hL1 : (43212427171813 / 100000000000000 : ℝ) ≤ Real.log (1 + (8648424754351 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8648424754351 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-12097175652249 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73520510549570 / 224117949835909 : ℝ) ≤ (316982470887763 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7352051054957 / 10000000000000 : ℝ) ≤ (316982470887763 / 500000000000000 : ℝ) := by
    have hw : (124117949835909 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7352051054957 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7352051054957 / 10000000000000 : ℝ) / (1 + (124117949835909 / 100000000000000 : ℝ)) = (73520510549570 / 224117949835909 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93683138501937061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 7352051054957 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 7352051054957 : ℝ) = (7352051054957 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 73520510549569 : ℝ) ≤ (101660677970091 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93683138501937061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7352051054957 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73520510549569 / 100000000000000 : ℝ)) ≤ (101660677970091 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_488 : ∀ t : ℝ, (8648424754351 / 16000000000000 : ℝ) < t → t ≤ (69267284916843 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-12142729369487842444683529 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (69267284916843 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_489
  have hV : (23521848406780898977880614933283561 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8648424754351 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_488 (Vfield_monotoneOn (show (8648424754351 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8648424754351 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_489 : (23536566210494971517251529002637601 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (69267284916843 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (69267284916843 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (73562943348729 / 100000000000000 : ℝ) ≤ Real.sqrt (69267284916843 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (69267284916843 / 128000000000000 : ℝ) ≤ (7356294334873 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7356294334873 / 10000000000000 : ℝ) = (10000000000000 / 7356294334873 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73562943348729 / 100000000000000 : ℝ) = (2500000000000 / 24520981116243 : ℝ) := by norm_num
  have hL1 : (21626466072841 / 50000000000000 : ℝ) ≤ Real.log (1 + (69267284916843 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((69267284916843 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-60371668215469 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (36781471674365 / 112071544676543 : ℝ) ≤ (317120164739737 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7356294334873 / 10000000000000 : ℝ) ≤ (317120164739737 / 500000000000000 : ℝ) := by
    have hw : (62071544676543 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (7356294334873 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7356294334873 / 10000000000000 : ℝ) / (1 + (62071544676543 / 50000000000000 : ℝ)) = (36781471674365 / 112071544676543 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93655599731542261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 7356294334873 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 7356294334873 : ℝ) = (7356294334873 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 24520981116243 : ℝ) ≤ (1270030507469 / 12500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93655599731542261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7356294334873 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73562943348729 / 100000000000000 : ℝ)) ≤ (1270030507469 / 12500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_489 : ∀ t : ℝ, (69267284916843 / 128000000000000 : ℝ) < t → t ≤ (34673585899439 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-6062140137528533123732789 / 6250000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (34673585899439 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_490
  have hV : (23536566210494971517251529002637601 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (69267284916843 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_489 (Vfield_monotoneOn (show (69267284916843 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (69267284916843 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_490 : (23551275842810695669649967190679051 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (34673585899439 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (34673585899439 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (73605351685779 / 100000000000000 : ℝ) ≤ Real.sqrt (34673585899439 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (34673585899439 / 64000000000000 : ℝ) ≤ (3680267584289 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3680267584289 / 5000000000000 : ℝ) = (5000000000000 / 3680267584289 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73605351685779 / 100000000000000 : ℝ) = (2500000000000 / 24535117228593 : ℝ) := by norm_num
  have hL1 : (2705838794979 / 6250000000000 : ℝ) ≤ Real.log (1 + (34673585899439 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((34673585899439 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-60257588460247 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73605351685780 / 224168223780431 : ℝ) ≤ (158628861747179 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3680267584289 / 5000000000000 : ℝ) ≤ (158628861747179 / 250000000000000 : ℝ) := by
    have hw : (124168223780431 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (3680267584289 / 5000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3680267584289 / 5000000000000 : ℝ) / (1 + (124168223780431 / 100000000000000 : ℝ)) = (73605351685780 / 224168223780431 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93628087980618061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 3680267584289 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 3680267584289 : ℝ) = (3680267584289 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 24535117228593 : ℝ) ≤ (50772151598507 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93628087980618061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3680267584289 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73605351685779 / 100000000000000 : ℝ)) ≤ (50772151598507 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_490 : ∀ t : ℝ, (34673585899439 / 64000000000000 : ℝ) < t → t ≤ (69427058680913 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-96847315910071806946475921 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (69427058680913 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_491
  have hV : (23551275842810695669649967190679051 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (34673585899439 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_490 (Vfield_monotoneOn (show (34673585899439 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (34673585899439 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_491 : (23565977316630807420247787121805851 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (69427058680913 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (69427058680913 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (73647735602979 / 100000000000000 : ℝ) ≤ Real.sqrt (69427058680913 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (69427058680913 / 128000000000000 : ℝ) ≤ (3682386780149 / 5000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (3682386780149 / 5000000000000 : ℝ) = (5000000000000 / 3682386780149 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73647735602979 / 100000000000000 : ℝ) = (2500000000000 / 24549245200993 : ℝ) := by norm_num
  have hL1 : (8666778581407 / 20000000000000 : ℝ) ≤ Real.log (1 + (69427058680913 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((69427058680913 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-60143638698649 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (18411933900745 / 56048338280259 : ℝ) ≤ (158697573699 / 500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (3682386780149 / 5000000000000 : ℝ) ≤ (158697573699 / 250000000000 : ℝ) := by
    have hw : (31048338280259 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (3682386780149 / 5000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (3682386780149 / 5000000000000 : ℝ) / (1 + (31048338280259 / 25000000000000 : ℝ)) = (18411933900745 / 56048338280259 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93600603199889661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (5000000000000 / 3682386780149 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (5000000000000 / 3682386780149 : ℝ) = (3682386780149 / 5000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 24549245200993 : ℝ) ≤ (25371566370717 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93600603199889661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (3682386780149 / 5000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73647735602979 / 100000000000000 : ℝ)) ≤ (25371566370717 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_491 : ∀ t : ℝ, (69427058680913 / 128000000000000 : ℝ) < t → t ≤ (17376736390737 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-48350519654849797203204367 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (17376736390737 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_492
  have hV : (23565977316630807420247787121805851 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (69427058680913 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_491 (Vfield_monotoneOn (show (69427058680913 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (69427058680913 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_492 : (23580670644822564346804968708609047 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (17376736390737 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (17376736390737 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (73690095142463 / 100000000000000 : ℝ) ≤ Real.sqrt (17376736390737 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (17376736390737 / 32000000000000 : ℝ) ≤ (1151407736601 / 1562500000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1151407736601 / 1562500000000 : ℝ) = (1562500000000 / 1151407736601 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73690095142463 / 100000000000000 : ℝ) = (7500000000000 / 73690095142463 : ℝ) := by norm_num
  have hL1 : (43374348721053 / 100000000000000 : ℝ) ≤ Real.log (1 + (17376736390737 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((17376736390737 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-60029818634757 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (36845047571232 / 112109238688993 : ℝ) ≤ (79383109174083 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1151407736601 / 1562500000000 : ℝ) ≤ (79383109174083 / 125000000000000 : ℝ) := by
    have hw : (62109238688993 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (1151407736601 / 1562500000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1151407736601 / 1562500000000 : ℝ) / (1 + (62109238688993 / 50000000000000 : ℝ)) = (36845047571232 / 112109238688993 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93573145340223261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1562500000000 / 1151407736601 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (1562500000000 / 1151407736601 : ℝ) = (1151407736601 / 1562500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 73690095142463 : ℝ) ≤ (50714163585263 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93573145340223261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1151407736601 / 1562500000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73690095142463 / 100000000000000 : ℝ)) ≤ (50714163585263 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_492 : ∀ t : ℝ, (17376736390737 / 32000000000000 : ℝ) < t → t ≤ (69586832444983 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-96555396521032404497054947 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (69586832444983 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_493
  have hV : (23580670644822564346804968708609047 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (17376736390737 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_492 (Vfield_monotoneOn (show (17376736390737 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (17376736390737 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_493 : (23595355840220705529865266508358943 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (69586832444983 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (69586832444983 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (73732430346247 / 100000000000000 : ℝ) ≤ Real.sqrt (69586832444983 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (69586832444983 / 128000000000000 : ℝ) ≤ (9216553793281 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9216553793281 / 12500000000000 : ℝ) = (12500000000000 / 9216553793281 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73732430346247 / 100000000000000 : ℝ) = (7500000000000 / 73732430346247 : ℝ) := by norm_num
  have hL1 : (542684852187 / 1250000000000 : ℝ) ≤ Real.log (1 + (69586832444983 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((69586832444983 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-59916127973661 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (36866215173124 / 112121798277183 : ℝ) ≤ (317669591634343 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9216553793281 / 12500000000000 : ℝ) ≤ (317669591634343 / 500000000000000 : ℝ) := by
    have hw : (62121798277183 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (9216553793281 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (9216553793281 / 12500000000000 : ℝ) / (1 + (62121798277183 / 50000000000000 : ℝ)) = (36866215173124 / 112121798277183 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93545714352621061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 9216553793281 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 9216553793281 : ℝ) = (9216553793281 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 73732430346247 : ℝ) ≤ (20274097595313 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93545714352621061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9216553793281 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73732430346247 / 100000000000000 : ℝ)) ≤ (20274097595313 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_493 : ∀ t : ℝ, (69586832444983 / 128000000000000 : ℝ) < t → t ≤ (34833359663509 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-3856414899754421982735249 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (34833359663509 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_494
  have hV : (23595355840220705529865266508358943 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (69586832444983 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_493 (Vfield_monotoneOn (show (69586832444983 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (69586832444983 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_494 : (23610032915627087728082144421833563 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (34833359663509 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (34833359663509 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (73774741256227 / 100000000000000 : ℝ) ≤ Real.sqrt (34833359663509 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (34833359663509 / 64000000000000 : ℝ) ≤ (18443685314057 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18443685314057 / 25000000000000 : ℝ) = (25000000000000 / 18443685314057 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73774741256227 / 100000000000000 : ℝ) = (7500000000000 / 73774741256227 : ℝ) := by norm_num
  have hL1 : (43455211281983 / 100000000000000 : ℝ) ≤ Real.log (1 + (34833359663509 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((34833359663509 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-59802566421459 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (36887370628114 / 112134355326629 : ℝ) ≤ (317806612456333 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18443685314057 / 25000000000000 : ℝ) ≤ (317806612456333 / 500000000000000 : ℝ) := by
    have hw : (62134355326629 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (18443685314057 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (18443685314057 / 25000000000000 : ℝ) / (1 + (62134355326629 / 50000000000000 : ℝ)) = (36887370628114 / 112134355326629 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93518310188223061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 18443685314057 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 18443685314057 : ℝ) = (18443685314057 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 73774741256227 : ℝ) ≤ (791505840771 / 7812500000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93518310188223061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18443685314057 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73774741256227 / 100000000000000 : ℝ)) ≤ (791505840771 / 7812500000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_494 : ∀ t : ℝ, (34833359663509 / 64000000000000 : ℝ) < t → t ≤ (69746606209053 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-48132976472045005497045777 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (69746606209053 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_495
  have hV : (23610032915627087728082144421833563 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (34833359663509 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_494 (Vfield_monotoneOn (show (34833359663509 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (34833359663509 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_495 : (369135966934515192705356567846271 / 78125000000000000000000000000000 : ℝ) ≤ Vfield (69746606209053 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (69746606209053 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (1153391061159 / 1562500000000 : ℝ) ≤ Real.sqrt (69746606209053 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (69746606209053 / 128000000000000 : ℝ) ≤ (73817027914177 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (73817027914177 / 100000000000000 : ℝ) = (100000000000000 / 73817027914177 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1153391061159 / 1562500000000 : ℝ) = (39062500000 / 384463687053 : ℝ) := by norm_num
  have hL1 : (43495618055333 / 100000000000000 : ℝ) ≤ Real.log (1 + (69746606209053 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((69746606209053 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-59689133685247 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73817027914177 / 224293819677739 : ℝ) ≤ (317943499405911 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (73817027914177 / 100000000000000 : ℝ) ≤ (317943499405911 / 500000000000000 : ℝ) := by
    have hw : (124293819677739 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (73817027914177 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (73817027914177 / 100000000000000 : ℝ) / (1 + (124293819677739 / 100000000000000 : ℝ)) = (73817027914177 / 224293819677739 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93490932798307461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 73817027914177 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 73817027914177 : ℝ) = (73817027914177 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (39062500000 / 384463687053 : ℝ) ≤ (10125510581573 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93490932798307461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (73817027914177 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1153391061159 / 1562500000000 : ℝ)) ≤ (10125510581573 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_495 : ∀ t : ℝ, (69746606209053 / 128000000000000 : ℝ) < t → t ≤ (4364155818193 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-96122124297647572733025679 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4364155818193 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_496
  have hV : (369135966934515192705356567846271 / 78125000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (69746606209053 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_495 (Vfield_monotoneOn (show (69746606209053 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (69746606209053 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_496 : (23639362757500992153967321079149981 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4364155818193 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4364155818193 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (73859290361749 / 100000000000000 : ℝ) ≤ Real.sqrt (4364155818193 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4364155818193 / 8000000000000 : ℝ) ≤ (295437161447 / 400000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (295437161447 / 400000000000 : ℝ) = (400000000000 / 295437161447 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73859290361749 / 100000000000000 : ℝ) = (7500000000000 / 73859290361749 : ℝ) := by norm_num
  have hL1 : (43536008508203 / 100000000000000 : ℝ) ≤ Real.log (1 + (4364155818193 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4364155818193 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-14893957368279 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (36929645180875 / 112159461815441 : ℝ) ≤ (318080252726011 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (295437161447 / 400000000000 : ℝ) ≤ (318080252726011 / 500000000000000 : ℝ) := by
    have hw : (62159461815441 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (295437161447 / 400000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (295437161447 / 400000000000 : ℝ) / (1 + (62159461815441 / 50000000000000 : ℝ)) = (36929645180875 / 112159461815441 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93463582134287461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (400000000000 / 295437161447 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (400000000000 / 295437161447 : ℝ) = (295437161447 / 400000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 73859290361749 : ℝ) ≤ (2529939057191 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93463582134287461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (295437161447 / 400000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73859290361749 / 100000000000000 : ℝ)) ≤ (2529939057191 / 25000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_496 : ∀ t : ℝ, (4364155818193 / 8000000000000 : ℝ) < t → t ≤ (69906379973123 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-47989436819801743415160971 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (69906379973123 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_497
  have hV : (23639362757500992153967321079149981 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4364155818193 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_496 (Vfield_monotoneOn (show (4364155818193 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4364155818193 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_497 : (23654015549405453913038812435686427 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (69906379973123 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (69906379973123 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (73901528640483 / 100000000000000 : ℝ) ≤ Real.sqrt (69906379973123 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (69906379973123 / 128000000000000 : ℝ) ≤ (18475382160121 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18475382160121 / 25000000000000 : ℝ) = (25000000000000 / 18475382160121 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (73901528640483 / 100000000000000 : ℝ) = (2500000000000 / 24633842880161 : ℝ) := by norm_num
  have hL1 : (21788191326887 / 50000000000000 : ℝ) ≤ Real.log (1 + (69906379973123 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((69906379973123 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1189253069883 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (73901528640484 / 224344022515761 : ℝ) ≤ (79554218164721 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18475382160121 / 25000000000000 : ℝ) ≤ (79554218164721 / 125000000000000 : ℝ) := by
    have hw : (124344022515761 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (18475382160121 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (18475382160121 / 25000000000000 : ℝ) / (1 + (124344022515761 / 100000000000000 : ℝ)) = (73901528640484 / 224344022515761 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93436258147712861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 18475382160121 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 18475382160121 : ℝ) = (18475382160121 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 24633842880161 : ℝ) ≤ (101140116755479 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93436258147712861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18475382160121 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (73901528640483 / 100000000000000 : ℝ)) ≤ (101140116755479 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_497 : ∀ t : ℝ, (69906379973123 / 128000000000000 : ℝ) < t → t ≤ (34993133427579 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23959047166982427175595341 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (34993133427579 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_498
  have hV : (23654015549405453913038812435686427 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (69906379973123 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_497 (Vfield_monotoneOn (show (69906379973123 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (69906379973123 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_498 : (4733732054438174268948443788993071 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (34993133427579 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (34993133427579 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (14788748558359 / 20000000000000 : ℝ) ≤ Real.sqrt (34993133427579 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (34993133427579 / 64000000000000 : ℝ) ≤ (18485935697949 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18485935697949 / 25000000000000 : ℝ) = (25000000000000 / 18485935697949 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14788748558359 / 20000000000000 : ℝ) = (1500000000000 / 14788748558359 : ℝ) := by norm_num
  have hL1 : (21808370252603 / 50000000000000 : ℝ) ≤ Real.log (1 + (34993133427579 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((34993133427579 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2967480272921 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (6161978565983 / 18697426361287 : ℝ) ≤ (159176679723053 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18485935697949 / 25000000000000 : ℝ) ≤ (159176679723053 / 250000000000000 : ℝ) := by
    have hw : (31092279083861 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (18485935697949 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (18485935697949 / 25000000000000 : ℝ) / (1 + (31092279083861 / 25000000000000 : ℝ)) = (6161978565983 / 18697426361287 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93408960790268461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 18485935697949 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 18485935697949 : ℝ) = (18485935697949 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 14788748558359 : ℝ) ≤ (50541384470709 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93408960790268461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18485935697949 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14788748558359 / 20000000000000 : ℝ)) ≤ (50541384470709 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_498 : ∀ t : ℝ, (34993133427579 / 64000000000000 : ℝ) < t → t ≤ (70066153737193 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-95694057651385764170624499 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (70066153737193 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_499
  have hV : (4733732054438174268948443788993071 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (34993133427579 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_498 (Vfield_monotoneOn (show (34993133427579 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (34993133427579 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_499 : (2960412117311659232053212129232587 / 625000000000000000000000000000000 : ℝ) ≤ Vfield (70066153737193 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (70066153737193 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (9248241607123 / 12500000000000 : ℝ) ≤ Real.sqrt (70066153737193 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (70066153737193 / 128000000000000 : ℝ) ≤ (14797186571397 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (14797186571397 / 20000000000000 : ℝ) = (20000000000000 / 14797186571397 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9248241607123 / 12500000000000 : ℝ) = (937500000000 / 9248241607123 : ℝ) := by norm_num
  have hL1 : (43657082075647 / 100000000000000 : ℝ) ≤ Real.log (1 + (70066153737193 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((70066153737193 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-3702292817311 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (14797186571397 / 44878841018599 : ℝ) ≤ (318489713328577 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (14797186571397 / 20000000000000 : ℝ) ≤ (318489713328577 / 500000000000000 : ℝ) := by
    have hw : (24878841018599 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (14797186571397 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (14797186571397 / 20000000000000 : ℝ) / (1 + (24878841018599 / 20000000000000 : ℝ)) = (14797186571397 / 44878841018599 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93381690013774261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 14797186571397 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 14797186571397 : ℝ) = (14797186571397 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (937500000000 / 9248241607123 : ℝ) ≤ (101025518568727 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93381690013774261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (14797186571397 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9248241607123 / 12500000000000 : ℝ)) ≤ (101025518568727 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_499 : ∀ t : ℝ, (70066153737193 / 128000000000000 : ℝ) < t → t ≤ (17536510154807 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23888117347772541796454567 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (17536510154807 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_500
  have hV : (2960412117311659232053212129232587 / 625000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (70066153737193 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_499 (Vfield_monotoneOn (show (70066153737193 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (70066153737193 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_500 : (23697925560915778168570418193325639 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (17536510154807 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (17536510154807 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (74028098877231 / 100000000000000 : ℝ) ≤ Real.sqrt (17536510154807 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (17536510154807 / 32000000000000 : ℝ) ≤ (4626756179827 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (4626756179827 / 6250000000000 : ℝ) = (6250000000000 / 4626756179827 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (74028098877231 / 100000000000000 : ℝ) = (2500000000000 / 24676032959077 : ℝ) := by norm_num
  have hL1 : (10924351844557 / 25000000000000 : ℝ) ≤ Real.log (1 + (17536510154807 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((17536510154807 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-7390486507731 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (37014049438616 / 112209644395739 : ℝ) ≤ (79656483636631 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (4626756179827 / 6250000000000 : ℝ) ≤ (79656483636631 / 125000000000000 : ℝ) := by
    have hw : (62209644395739 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (4626756179827 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (4626756179827 / 6250000000000 : ℝ) / (1 + (62209644395739 / 50000000000000 : ℝ)) = (37014049438616 / 112209644395739 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93354445770184861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 4626756179827 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 4626756179827 : ℝ) = (4626756179827 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 24676032959077 : ℝ) ≤ (4038734614471 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93354445770184861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (4626756179827 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (74028098877231 / 100000000000000 : ℝ)) ≤ (4038734614471 / 40000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_500 : ∀ t : ℝ, (17536510154807 / 32000000000000 : ℝ) < t → t ≤ (35152907191649 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23817719699420456005967049 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (35152907191649 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_501
  have hV : (23697925560915778168570418193325639 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (17536510154807 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_500 (Vfield_monotoneOn (show (17536510154807 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (17536510154807 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_501 : (23727158724372230601043460017859529 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (35152907191649 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (35152907191649 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (74112358947041 / 100000000000000 : ℝ) ≤ Real.sqrt (35152907191649 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (35152907191649 / 64000000000000 : ℝ) ≤ (37056179473521 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (37056179473521 / 50000000000000 : ℝ) = (50000000000000 / 37056179473521 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (74112358947041 / 100000000000000 : ℝ) = (7500000000000 / 74112358947041 : ℝ) := by norm_num
  have hL1 : (175112036929 / 400000000000 : ℝ) ≤ Real.log (1 + (35152907191649 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((35152907191649 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-58898686983523 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (37056179473521 / 112234720511735 : ℝ) ≤ (79724494986607 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (37056179473521 / 50000000000000 : ℝ) ≤ (79724494986607 / 125000000000000 : ℝ) := by
    have hw : (12446944102347 / 10000000000000 : ℝ) ≤ Real.sqrt (1 + (37056179473521 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (37056179473521 / 50000000000000 : ℝ) / (1 + (12446944102347 / 10000000000000 : ℝ)) = (37056179473521 / 112234720511735 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93300036690204061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 37056179473521 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 37056179473521 : ℝ) = (37056179473521 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 74112358947041 : ℝ) ≤ (100854349347997 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93300036690204061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (37056179473521 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (74112358947041 / 100000000000000 : ℝ)) ≤ (100854349347997 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_501 : ∀ t : ℝ, (35152907191649 / 64000000000000 : ℝ) < t → t ≤ (8808198518421 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18998267336086891952798567 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8808198518421 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_502
  have hV : (23727158724372230601043460017859529 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (35152907191649 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_501 (Vfield_monotoneOn (show (35152907191649 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (35152907191649 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_502 : (23756359862737678027224051202379229 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (8808198518421 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8808198518421 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (74196523328341 / 100000000000000 : ℝ) ≤ Real.sqrt (8808198518421 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8808198518421 / 16000000000000 : ℝ) ≤ (37098261664171 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (37098261664171 / 50000000000000 : ℝ) = (50000000000000 / 37098261664171 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (74196523328341 / 100000000000000 : ℝ) = (7500000000000 / 74196523328341 : ℝ) := by norm_num
  have hL1 : (43858546172003 / 100000000000000 : ℝ) ≤ Real.log (1 + (8808198518421 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8808198518421 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-58673987939071 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (37098261664171 / 112259786527929 : ℝ) ≤ (63833899510863 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (37098261664171 / 50000000000000 : ℝ) ≤ (63833899510863 / 100000000000000 : ℝ) := by
    have hw : (62259786527929 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (37098261664171 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (37098261664171 / 50000000000000 : ℝ) / (1 + (62259786527929 / 50000000000000 : ℝ)) = (37098261664171 / 112259786527929 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93245733168626661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 37098261664171 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 37098261664171 : ℝ) = (37098261664171 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 74196523328341 : ℝ) ≤ (10074071871673 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93245733168626661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (37098261664171 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (74196523328341 / 100000000000000 : ℝ)) ≤ (10074071871673 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_502 : ∀ t : ℝ, (8808198518421 / 16000000000000 : ℝ) < t → t ≤ (35312680955719 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18942753877225627934194971 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (35312680955719 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_503
  have hV : (23756359862737678027224051202379229 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8808198518421 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_502 (Vfield_monotoneOn (show (8808198518421 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8808198518421 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_503 : (23785529075673819947078522649881217 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (35312680955719 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (35312680955719 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (74280592346393 / 100000000000000 : ℝ) ≤ Real.sqrt (35312680955719 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (35312680955719 / 64000000000000 : ℝ) ≤ (37140296173197 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (37140296173197 / 50000000000000 : ℝ) = (50000000000000 / 37140296173197 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (74280592346393 / 100000000000000 : ℝ) = (7500000000000 / 74280592346393 : ℝ) := by norm_num
  have hL1 : (21969509150981 / 50000000000000 : ℝ) ≤ Real.log (1 + (35312680955719 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((35312680955719 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-58449792659481 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (1768585532057 / 5346897259834 : ℝ) ≤ (159720244634051 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (37140296173197 / 50000000000000 : ℝ) ≤ (159720244634051 / 250000000000000 : ℝ) := by
    have hw : (31142421228257 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (37140296173197 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (37140296173197 / 50000000000000 : ℝ) / (1 + (31142421228257 / 25000000000000 : ℝ)) = (1768585532057 / 5346897259834 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93191534825869261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 37140296173197 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 37140296173197 : ℝ) = (37140296173197 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 74280592346393 : ℝ) ≤ (50313735650899 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93191534825869261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (37140296173197 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (74280592346393 / 100000000000000 : ℝ)) ≤ (50313735650899 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_503 : ∀ t : ℝ, (35312680955719 / 64000000000000 : ℝ) < t → t ≤ (17696283918877 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-94438109036735988279862859 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (17696283918877 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_504
  have hV : (23785529075673819947078522649881217 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (35312680955719 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_503 (Vfield_monotoneOn (show (35312680955719 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (35312680955719 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_504 : (23814666462330744415019084905518549 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (17696283918877 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (17696283918877 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (74364566324621 / 100000000000000 : ℝ) ≤ Real.sqrt (17696283918877 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (17696283918877 / 32000000000000 : ℝ) ≤ (37182283162311 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (37182283162311 / 50000000000000 : ℝ) = (50000000000000 / 37182283162311 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (74364566324621 / 100000000000000 : ℝ) = (7500000000000 / 74364566324621 : ℝ) := by norm_num
  have hL1 : (44019425726349 / 100000000000000 : ℝ) ≤ Real.log (1 + (17696283918877 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((17696283918877 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5822609889097 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (74364566324622 / 224619776619319 : ℝ) ≤ (79927739243801 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (37182283162311 / 50000000000000 : ℝ) ≤ (79927739243801 / 125000000000000 : ℝ) := by
    have hw : (124619776619319 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (37182283162311 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (37182283162311 / 50000000000000 : ℝ) / (1 + (124619776619319 / 100000000000000 : ℝ)) = (74364566324622 / 224619776619319 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93137441284448861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 37182283162311 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 37182283162311 : ℝ) = (37182283162311 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 74364566324621 : ℝ) ≤ (20102920990807 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93137441284448861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (37182283162311 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (74364566324621 / 100000000000000 : ℝ)) ≤ (20102920990807 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_504 : ∀ t : ℝ, (17696283918877 / 32000000000000 : ℝ) < t → t ≤ (35472454719789 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23541073221310274763963289 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (35472454719789 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_505
  have hV : (23814666462330744415019084905518549 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (17696283918877 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_504 (Vfield_monotoneOn (show (17696283918877 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (17696283918877 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_505 : (11921886060675530589175404381793697 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (35472454719789 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (35472454719789 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (37224222792313 / 50000000000000 : ℝ) ≤ Real.sqrt (35472454719789 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (35472454719789 / 64000000000000 : ℝ) ≤ (74448445584627 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (74448445584627 / 100000000000000 : ℝ) = (100000000000000 / 74448445584627 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (37224222792313 / 50000000000000 : ℝ) = (3750000000000 / 37224222792313 : ℝ) := by norm_num
  have hL1 : (44099768549139 / 100000000000000 : ℝ) ≤ Real.log (1 + (35472454719789 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((35472454719789 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-58002904394847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (74448445584627 / 224669848199021 : ℝ) ≤ (319980902552623 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (74448445584627 / 100000000000000 : ℝ) ≤ (319980902552623 / 500000000000000 : ℝ) := by
    have hw : (124669848199021 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (74448445584627 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (74448445584627 / 100000000000000 : ℝ) / (1 + (124669848199021 / 100000000000000 : ℝ)) = (74448445584627 / 224669848199021 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93083452168965061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 74448445584627 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 74448445584627 : ℝ) = (74448445584627 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 37224222792313 : ℝ) ≤ (10040211754111 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93083452168965061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (74448445584627 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (37224222792313 / 50000000000000 : ℝ)) ≤ (10040211754111 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_505 : ∀ t : ℝ, (35472454719789 / 64000000000000 : ℝ) < t → t ≤ (1111010675057 / 2000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-3755690509801747137002687 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1111010675057 / 2000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_506
  have hV : (11921886060675530589175404381793697 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (35472454719789 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_505 (Vfield_monotoneOn (show (35472454719789 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (35472454719789 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_506 : (5968211537717891565813356431046181 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (1111010675057 / 2000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1111010675057 / 2000000000000 : ℝ) := by norm_num
  have hs1 : (18633057611549 / 25000000000000 : ℝ) ≤ Real.sqrt (1111010675057 / 2000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1111010675057 / 2000000000000 : ℝ) ≤ (74532230446197 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (74532230446197 / 100000000000000 : ℝ) = (100000000000000 / 74532230446197 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (18633057611549 / 25000000000000 : ℝ) = (1875000000000 / 18633057611549 : ℝ) := by norm_num
  have hL1 : (44180046874053 / 100000000000000 : ℝ) ≤ Real.log (1 + (1111010675057 / 2000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1111010675057 / 2000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-462241655579 / 800000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (24844076815399 / 74906633225458 : ℝ) ≤ (2501955686461 / 7812500000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (74532230446197 / 100000000000000 : ℝ) ≤ (2501955686461 / 3906250000000 : ℝ) := by
    have hw : (62359949838187 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (74532230446197 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (74532230446197 / 100000000000000 : ℝ) / (1 + (62359949838187 / 50000000000000 : ℝ)) = (24844076815399 / 74906633225458 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (93029567106088061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 74532230446197 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 74532230446197 : ℝ) = (74532230446197 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 18633057611549 : ℝ) ≤ (25072501736841 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (93029567106088061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (74532230446197 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (18633057611549 / 25000000000000 : ℝ)) ≤ (25072501736841 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_506 : ∀ t : ℝ, (1111010675057 / 2000000000000 : ℝ) < t → t ≤ (35632228483859 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18724392901535591698427173 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (35632228483859 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_507
  have hV : (5968211537717891565813356431046181 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1111010675057 / 2000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_506 (Vfield_monotoneOn (show (1111010675057 / 2000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1111010675057 / 2000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_507 : (23901888648530387178449338681681001 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (35632228483859 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (35632228483859 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (74615921227329 / 100000000000000 : ℝ) ≤ Real.sqrt (35632228483859 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (35632228483859 / 64000000000000 : ℝ) ≤ (7461592122733 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7461592122733 / 10000000000000 : ℝ) = (10000000000000 / 7461592122733 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (74615921227329 / 100000000000000 : ℝ) = (2500000000000 / 24871973742443 : ℝ) := by norm_num
  have hL1 : (11065065201141 / 25000000000000 : ℝ) ≤ Real.log (1 + (35632228483859 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((35632228483859 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-57558004339643 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (37307960613665 / 112384965537786 : ℝ) ≤ (320519234774767 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7461592122733 / 10000000000000 : ℝ) ≤ (320519234774767 / 500000000000000 : ℝ) := by
    have hw : (31192482768893 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (7461592122733 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7461592122733 / 10000000000000 : ℝ) / (1 + (31192482768893 / 25000000000000 : ℝ)) = (37307960613665 / 112384965537786 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92975785724536261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 7461592122733 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 7461592122733 : ℝ) = (7461592122733 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 24871973742443 : ℝ) ≤ (100178271073629 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92975785724536261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7461592122733 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (74615921227329 / 100000000000000 : ℝ)) ≤ (100178271073629 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_507 : ∀ t : ℝ, (35632228483859 / 64000000000000 : ℝ) < t → t ≤ (17856057682947 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23338336930911756573135467 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (17856057682947 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_508
  have hV : (23901888648530387178449338681681001 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (35632228483859 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_507 (Vfield_monotoneOn (show (35632228483859 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (35632228483859 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_508 : (4786179942293183993351617387458343 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (17856057682947 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (17856057682947 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (14939903648847 / 20000000000000 : ℝ) ≤ Real.sqrt (17856057682947 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (17856057682947 / 32000000000000 : ℝ) ≤ (18674879561059 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18674879561059 / 25000000000000 : ℝ) = (25000000000000 / 18674879561059 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (14939903648847 / 20000000000000 : ℝ) = (500000000000 / 4979967882949 : ℝ) := by norm_num
  have hL1 : (5542551305487 / 12500000000000 : ℝ) ≤ Real.log (1 + (17856057682947 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((17856057682947 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-57336294377431 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (18674879561059 / 56204985605189 : ℝ) ≤ (320787625122103 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18674879561059 / 25000000000000 : ℝ) ≤ (320787625122103 / 500000000000000 : ℝ) := by
    have hw : (31204985605189 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (18674879561059 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (18674879561059 / 25000000000000 : ℝ) / (1 + (31204985605189 / 25000000000000 : ℝ)) = (18674879561059 / 56204985605189 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92922107655069061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 18674879561059 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 18674879561059 : ℝ) = (18674879561059 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 4979967882949 : ℝ) ≤ (100066907837083 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92922107655069061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18674879561059 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (14939903648847 / 20000000000000 : ℝ)) ≤ (100066907837083 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_508 : ∀ t : ℝ, (17856057682947 / 32000000000000 : ℝ) < t → t ≤ (35792002247929 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-93086365237977820806804017 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (35792002247929 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_509
  have hV : (4786179942293183993351617387458343 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (17856057682947 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_508 (Vfield_monotoneOn (show (17856057682947 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (17856057682947 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_509 : (23959879436325041513197760910693147 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (35792002247929 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (35792002247929 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (74783021811363 / 100000000000000 : ℝ) ≤ Real.sqrt (35792002247929 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (35792002247929 / 64000000000000 : ℝ) ≤ (18695755452841 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18695755452841 / 25000000000000 : ℝ) = (25000000000000 / 18695755452841 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (74783021811363 / 100000000000000 : ℝ) = (2500000000000 / 24927673937121 : ℝ) := by norm_num
  have hL1 : (44420495895023 / 100000000000000 : ℝ) ≤ Real.log (1 + (35792002247929 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((35792002247929 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-57115074881081 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (74783021811364 / 224869933736023 : ℝ) ≤ (160527750372567 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18695755452841 / 25000000000000 : ℝ) ≤ (160527750372567 / 250000000000000 : ℝ) := by
    have hw : (124869933736023 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (18695755452841 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (18695755452841 / 25000000000000 : ℝ) / (1 + (124869933736023 / 100000000000000 : ℝ)) = (74783021811364 / 224869933736023 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92868532530462861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 18695755452841 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 18695755452841 : ℝ) = (18695755452841 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 24927673937121 : ℝ) ≤ (24988978792767 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92868532530462861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18695755452841 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (74783021811363 / 100000000000000 : ℝ)) ≤ (24988978792767 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_509 : ∀ t : ℝ, (35792002247929 / 64000000000000 : ℝ) < t → t ≤ (8967972282491 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-92820972871966994974082019 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (8967972282491 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_510
  have hV : (23959879436325041513197760910693147 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (35792002247929 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_509 (Vfield_monotoneOn (show (35792002247929 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (35792002247929 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_510 : (5997206979815791177300255300544919 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (8967972282491 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (8967972282491 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (18716608060351 / 25000000000000 : ℝ) ≤ Real.sqrt (8967972282491 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (8967972282491 / 16000000000000 : ℝ) ≤ (14973286448281 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (14973286448281 / 20000000000000 : ℝ) = (20000000000000 / 14973286448281 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (18716608060351 / 25000000000000 : ℝ) = (1875000000000 / 18716608060351 : ℝ) := by norm_num
  have hL1 : (11125129315169 / 25000000000000 : ℝ) ≤ Real.log (1 + (8967972282491 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((8967972282491 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-56894343685369 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (14973286448281 / 44983981009084 : ℝ) ≤ (64264572693987 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (14973286448281 / 20000000000000 : ℝ) ≤ (64264572693987 / 100000000000000 : ℝ) := by
    have hw : (6245995252271 / 5000000000000 : ℝ) ≤ Real.sqrt (1 + (14973286448281 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (14973286448281 / 20000000000000 : ℝ) / (1 + (6245995252271 / 5000000000000 : ℝ)) = (14973286448281 / 44983981009084 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92815059985502661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 14973286448281 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 14973286448281 : ℝ) = (14973286448281 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 18716608060351 : ℝ) ≤ (99845291024941 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92815059985502661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (14973286448281 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (18716608060351 / 25000000000000 : ℝ)) ≤ (99845291024941 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_510 : ∀ t : ℝ, (8967972282491 / 16000000000000 : ℝ) < t → t ≤ (35951776011999 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23139282286032978634006501 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (35951776011999 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_511
  have hV : (5997206979815791177300255300544919 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (8967972282491 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_510 (Vfield_monotoneOn (show (8967972282491 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (8967972282491 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_511 : (24017745255949456649446920431779159 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (35951776011999 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (35951776011999 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (74949749845311 / 100000000000000 : ℝ) ≤ Real.sqrt (35951776011999 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (35951776011999 / 64000000000000 : ℝ) ≤ (1171089841333 / 1562500000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1171089841333 / 1562500000000 : ℝ) = (1562500000000 / 1171089841333 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (74949749845311 / 100000000000000 : ℝ) = (2500000000000 / 24983249948437 : ℝ) := by norm_num
  have hL1 : (5572559330417 / 12500000000000 : ℝ) ≤ Real.log (1 + (35951776011999 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((35951776011999 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-28337049319689 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (37474874922656 / 112484928186473 : ℝ) ≤ (321589715112633 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1171089841333 / 1562500000000 : ℝ) ≤ (321589715112633 / 500000000000000 : ℝ) := by
    have hw : (62484928186473 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (1171089841333 / 1562500000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1171089841333 / 1562500000000 : ℝ) / (1 + (62484928186473 / 50000000000000 : ℝ)) = (37474874922656 / 112484928186473 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92761689656963061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1562500000000 / 1171089841333 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (1562500000000 / 1171089841333 : ℝ) = (1171089841333 / 1562500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 24983249948437 : ℝ) ≤ (9973503336391 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92761689656963061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1171089841333 / 1562500000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (74949749845311 / 100000000000000 : ℝ)) ≤ (9973503336391 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_511 : ∀ t : ℝ, (35951776011999 / 64000000000000 : ℝ) < t → t ≤ (18015831447017 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-46147397512293419674889019 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (18015831447017 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_512
  have hV : (24017745255949456649446920431779159 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (35951776011999 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_511 (Vfield_monotoneOn (show (35951776011999 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (35951776011999 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_512 : (24046631541569902865600206168682159 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (18015831447017 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (18015831447017 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (75032974932311 / 100000000000000 : ℝ) ≤ Real.sqrt (18015831447017 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (18015831447017 / 32000000000000 : ℝ) ≤ (9379121866539 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (9379121866539 / 12500000000000 : ℝ) = (12500000000000 / 9379121866539 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (75032974932311 / 100000000000000 : ℝ) = (7500000000000 / 75032974932311 : ℝ) := by norm_num
  have hL1 : (44660368145239 / 100000000000000 : ℝ) ≤ Real.log (1 + (18015831447017 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((18015831447017 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5645433760637 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (3126373955513 / 9375824489273 : ℝ) ≤ (160928028739741 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (9379121866539 / 12500000000000 : ℝ) ≤ (160928028739741 / 250000000000000 : ℝ) := by
    have hw : (15627473467819 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (9379121866539 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (9379121866539 / 12500000000000 : ℝ) / (1 + (15627473467819 / 12500000000000 : ℝ)) = (3126373955513 / 9375824489273 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92708421183593261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 9379121866539 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 9379121866539 : ℝ) = (9379121866539 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 75032974932311 : ℝ) ≤ (99625140168877 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92708421183593261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (9379121866539 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (75032974932311 / 100000000000000 : ℝ)) ≤ (99625140168877 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_512 : ∀ t : ℝ, (18015831447017 / 32000000000000 : ℝ) < t → t ≤ (36111549776069 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-92033933718052299152889191 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (36111549776069 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_513
  have hV : (24046631541569902865600206168682159 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (18015831447017 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_512 (Vfield_monotoneOn (show (18015831447017 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (18015831447017 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_513 : (4815097374165957832711708423619927 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (36111549776069 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (36111549776069 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (15023221561983 / 20000000000000 : ℝ) ≤ Real.sqrt (36111549776069 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (36111549776069 / 64000000000000 : ℝ) ≤ (18779026952479 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (18779026952479 / 25000000000000 : ℝ) = (25000000000000 / 18779026952479 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (15023221561983 / 20000000000000 : ℝ) = (500000000000 / 5007740520661 : ℝ) := by norm_num
  have hL1 : (22370098934189 / 50000000000000 : ℝ) ≤ Real.log (1 + (36111549776069 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((36111549776069 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-11247011692733 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (75116107809916 / 225069699178141 : ℝ) ≤ (8053047309173 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (18779026952479 / 25000000000000 : ℝ) ≤ (8053047309173 / 12500000000000 : ℝ) := by
    have hw : (125069699178141 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (18779026952479 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (18779026952479 / 25000000000000 : ℝ) / (1 + (125069699178141 / 100000000000000 : ℝ)) = (75116107809916 / 225069699178141 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92655254206105661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 18779026952479 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 18779026952479 : ℝ) = (18779026952479 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 5007740520661 : ℝ) ≤ (49757804718143 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92655254206105661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (18779026952479 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (15023221561983 / 20000000000000 : ℝ)) ≤ (49757804718143 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_513 : ∀ t : ℝ, (36111549776069 / 64000000000000 : ℝ) < t → t ≤ (4523929582263 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2294362761787396659091721 / 2500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4523929582263 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_514
  have hV : (4815097374165957832711708423619927 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (36111549776069 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_513 (Vfield_monotoneOn (show (36111549776069 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (36111549776069 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_514 : (24104311337958713460617766101792553 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (4523929582263 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4523929582263 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (75199148783937 / 100000000000000 : ℝ) ≤ Real.sqrt (4523929582263 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4523929582263 / 8000000000000 : ℝ) ≤ (37599574391969 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (37599574391969 / 50000000000000 : ℝ) = (50000000000000 / 37599574391969 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (75199148783937 / 100000000000000 : ℝ) = (2500000000000 / 25066382927979 : ℝ) := by norm_num
  have hL1 : (44819963914499 / 100000000000000 : ℝ) ≤ Real.log (1 + (4523929582263 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4523929582263 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-11203251820503 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (75199148783938 / 225119590703569 : ℝ) ≤ (322387221561663 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (37599574391969 / 50000000000000 : ℝ) ≤ (322387221561663 / 500000000000000 : ℝ) := by
    have hw : (125119590703569 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (37599574391969 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (37599574391969 / 50000000000000 : ℝ) / (1 + (125119590703569 / 100000000000000 : ℝ)) = (75199148783938 / 225119590703569 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92602188367157061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 37599574391969 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 37599574391969 : ℝ) = (37599574391969 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 25066382927979 : ℝ) ≤ (24851609794491 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92602188367157061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (37599574391969 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (75199148783937 / 100000000000000 : ℝ)) ≤ (24851609794491 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_514 : ∀ t : ℝ, (4523929582263 / 8000000000000 : ℝ) < t → t ≤ (18175605211087 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-22814962087346821814761741 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (18175605211087 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_515
  have hV : (24104311337958713460617766101792553 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4523929582263 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_514 (Vfield_monotoneOn (show (4523929582263 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4523929582263 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_515 : (24161868060379407444092127585502061 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (18175605211087 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (18175605211087 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (75364956236069 / 100000000000000 : ℝ) ≤ Real.sqrt (18175605211087 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (18175605211087 / 32000000000000 : ℝ) ≤ (7536495623607 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7536495623607 / 10000000000000 : ℝ) = (10000000000000 / 7536495623607 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (75364956236069 / 100000000000000 : ℝ) = (7500000000000 / 75364956236069 : ℝ) := by norm_num
  have hL1 : (8995861076293 / 20000000000000 : ℝ) ≤ Real.log (1 + (18175605211087 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((18175605211087 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-13895022839707 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (75364956236070 / 225219314119127 : ℝ) ≤ (8072909249293 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7536495623607 / 10000000000000 : ℝ) ≤ (8072909249293 / 12500000000000 : ℝ) := by
    have hw : (125219314119127 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (7536495623607 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7536495623607 / 10000000000000 : ℝ) / (1 + (125219314119127 / 100000000000000 : ℝ)) = (75364956236070 / 225219314119127 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92496358685145661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 7536495623607 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 7536495623607 : ℝ) = (7536495623607 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 75364956236069 : ℝ) ≤ (4959458610373 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92496358685145661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7536495623607 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (75364956236069 / 100000000000000 : ℝ)) ≤ (4959458610373 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_515 : ∀ t : ℝ, (18175605211087 / 32000000000000 : ℝ) < t → t ≤ (9127746046561 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-90750565420349536001990263 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9127746046561 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_516
  have hV : (24161868060379407444092127585502061 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (18175605211087 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_515 (Vfield_monotoneOn (show (18175605211087 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (18175605211087 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_516 : (24219302453263794179985653688122297 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (9127746046561 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (9127746046561 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (75530399701713 / 100000000000000 : ℝ) ≤ Real.sqrt (9127746046561 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (9127746046561 / 16000000000000 : ℝ) ≤ (37765199850857 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (37765199850857 / 50000000000000 : ℝ) = (50000000000000 / 37765199850857 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (75530399701713 / 100000000000000 : ℝ) = (2500000000000 / 25176799900571 : ℝ) := by norm_num
  have hL1 : (22569196677633 / 50000000000000 : ℝ) ≤ Real.log (1 + (9127746046561 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((9127746046561 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-13786454444851 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (37765199850857 / 112659479089561 : ℝ) ≤ (323443516811531 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (37765199850857 / 50000000000000 : ℝ) ≤ (323443516811531 / 500000000000000 : ℝ) := by
    have hw : (62659479089561 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (37765199850857 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (37765199850857 / 50000000000000 : ℝ) / (1 + (62659479089561 / 50000000000000 : ℝ)) = (37765199850857 / 112659479089561 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92390929317183461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 37765199850857 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 37765199850857 : ℝ) = (37765199850857 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 25176799900571 : ℝ) ≤ (49486661826997 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92390929317183461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (37765199850857 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (75530399701713 / 100000000000000 : ℝ)) ≤ (49486661826997 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_516 : ∀ t : ℝ, (9127746046561 / 16000000000000 : ℝ) < t → t ≤ (18335378975157 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-22561610473920337498326861 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (18335378975157 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_517
  have hV : (24219302453263794179985653688122297 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (9127746046561 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_516 (Vfield_monotoneOn (show (9127746046561 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (9127746046561 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_517 : (4855323050726189164287114139767269 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (18335378975157 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (18335378975157 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (15139096313501 / 20000000000000 : ℝ) ≤ Real.sqrt (18335378975157 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (18335378975157 / 32000000000000 : ℝ) ≤ (37847740783753 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (37847740783753 / 50000000000000 : ℝ) = (50000000000000 / 37847740783753 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (15139096313501 / 20000000000000 : ℝ) = (1500000000000 / 15139096313501 : ℝ) := by norm_num
  have hL1 : (5662153580147 / 12500000000000 : ℝ) ≤ Real.log (1 + (18335378975157 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((18335378975157 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-27356710991809 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (75695481567506 / 225418523072697 : ℝ) ≤ (20248042251993 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (37847740783753 / 50000000000000 : ℝ) ≤ (20248042251993 / 31250000000000 : ℝ) := by
    have hw : (125418523072697 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (37847740783753 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (37847740783753 / 50000000000000 : ℝ) / (1 + (125418523072697 / 100000000000000 : ℝ)) = (75695481567506 / 225418523072697 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92285897473112061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 37847740783753 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 37847740783753 : ℝ) = (37847740783753 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 15139096313501 : ℝ) ≤ (98758878150857 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92285897473112061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (37847740783753 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (15139096313501 / 20000000000000 : ℝ)) ≤ (98758878150857 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_517 : ∀ t : ℝ, (18335378975157 / 32000000000000 : ℝ) < t → t ≤ (2301908232149 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2804602439447657232446183 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2301908232149 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_518
  have hV : (4855323050726189164287114139767269 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (18335378975157 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_517 (Vfield_monotoneOn (show (18335378975157 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (18335378975157 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_518 : (380215737362340680501666715024877 / 78125000000000000000000000000000 : ℝ) ≤ Vfield (2301908232149 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2301908232149 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (1185315690533 / 1562500000000 : ℝ) ≤ Real.sqrt (2301908232149 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2301908232149 / 4000000000000 : ℝ) ≤ (75860204194113 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (75860204194113 / 100000000000000 : ℝ) = (100000000000000 / 75860204194113 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (1185315690533 / 1562500000000 : ℝ) = (117187500000 / 1185315690533 : ℝ) := by norm_num
  have hL1 : (45455812040637 / 100000000000000 : ℝ) ≤ Real.log (1 + (2301908232149 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2301908232149 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-27141443901209 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (75860204194113 / 225518008988242 : ℝ) ≤ (81122965358683 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (75860204194113 / 100000000000000 : ℝ) ≤ (81122965358683 / 125000000000000 : ℝ) := by
    have hw : (62759004494121 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (75860204194113 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (75860204194113 / 100000000000000 : ℝ) / (1 + (62759004494121 / 50000000000000 : ℝ)) = (75860204194113 / 225518008988242 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92181260392543261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 75860204194113 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 75860204194113 : ℝ) = (75860204194113 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (117187500000 / 1185315690533 : ℝ) ≤ (49272910281703 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92181260392543261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (75860204194113 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (1185315690533 / 1562500000000 : ℝ)) ≤ (49272910281703 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_518 : ∀ t : ℝ, (2301908232149 / 4000000000000 : ℝ) < t → t ≤ (18495152739227 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-89252891507239271735454249 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (18495152739227 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_519
  have hV : (380215737362340680501666715024877 / 78125000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2301908232149 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_518 (Vfield_monotoneOn (show (2301908232149 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2301908232149 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_519 : (24390878988441481904311318905052701 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (18495152739227 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (18495152739227 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (76024569916629 / 100000000000000 : ℝ) ≤ Real.sqrt (18495152739227 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (18495152739227 / 32000000000000 : ℝ) ≤ (7602456991663 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (7602456991663 / 10000000000000 : ℝ) = (10000000000000 / 7602456991663 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (76024569916629 / 100000000000000 : ℝ) = (2500000000000 / 25341523305543 : ℝ) := by norm_num
  have hL1 : (9122828870257 / 20000000000000 : ℝ) ≤ Real.log (1 + (18495152739227 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((18495152739227 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-53854199274701 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (15204913983326 / 45123483222681 : ℝ) ≤ (6500261733507 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (7602456991663 / 10000000000000 : ℝ) ≤ (6500261733507 / 10000000000000 : ℝ) := by
    have hw : (25123483222681 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (7602456991663 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (7602456991663 / 10000000000000 : ℝ) / (1 + (25123483222681 / 20000000000000 : ℝ)) = (15204913983326 / 45123483222681 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (92077015344419661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 7602456991663 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 7602456991663 : ℝ) = (7602456991663 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 25341523305543 : ℝ) ≤ (1536470874759 / 15625000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (92077015344419661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (7602456991663 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (76024569916629 / 100000000000000 : ℝ)) ≤ (1536470874759 / 15625000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_519 : ∀ t : ℝ, (18495152739227 / 32000000000000 : ℝ) < t → t ≤ (9287519810631 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-44381557433099363247875217 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (9287519810631 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_520
  have hV : (24390878988441481904311318905052701 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (18495152739227 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_519 (Vfield_monotoneOn (show (18495152739227 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (18495152739227 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
