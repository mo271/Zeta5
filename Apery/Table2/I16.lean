import Apery.Table2.U16
import Apery.Table2.U17

set_option maxHeartbeats 4000000

namespace Apery

lemma V_pt_640 : (27886257853512648515588171664657927 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (11854766575033 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11854766575033 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (86076879063983 / 100000000000000 : ℝ) ≤ Real.sqrt (11854766575033 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11854766575033 / 16000000000000 : ℝ) ≤ (5379804941499 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5379804941499 / 6250000000000 : ℝ) = (6250000000000 / 5379804941499 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (86076879063983 / 100000000000000 : ℝ) = (7500000000000 / 86076879063983 : ℝ) := by norm_num
  have hL1 : (55441538119547 / 100000000000000 : ℝ) ≤ Real.log (1 + (11854766575033 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11854766575033 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-14614774151973 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (43038439531992 / 115972018897021 : ℝ) ≤ (71071277485329 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5379804941499 / 6250000000000 : ℝ) ≤ (71071277485329 / 100000000000000 : ℝ) := by
    have hw : (65972018897021 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (5379804941499 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (5379804941499 / 6250000000000 : ℝ) / (1 + (65972018897021 / 50000000000000 : ℝ)) = (43038439531992 / 115972018897021 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (86008355194160661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 5379804941499 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 5379804941499 : ℝ) = (5379804941499 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 86076879063983 : ℝ) ≤ (86911913663471 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (86008355194160661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5379804941499 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (86076879063983 / 100000000000000 : ℝ)) ≤ (86911913663471 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_640 : ∀ t : ℝ, (11854766575033 / 16000000000000 : ℝ) < t → t ≤ (23740009868623 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-26764469752149586909481961 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23740009868623 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_641
  have hV : (27886257853512648515588171664657927 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11854766575033 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_640 (Vfield_monotoneOn (show (11854766575033 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11854766575033 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_641 : (27905505072544574460930611624968733 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (23740009868623 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23740009868623 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (86132183787157 / 100000000000000 : ℝ) ≤ Real.sqrt (23740009868623 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23740009868623 / 32000000000000 : ℝ) ≤ (43066091893579 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (43066091893579 / 50000000000000 : ℝ) = (50000000000000 / 43066091893579 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (86132183787157 / 100000000000000 : ℝ) = (7500000000000 / 86132183787157 : ℝ) := by norm_num
  have hL1 : (27748114815073 / 50000000000000 : ℝ) ≤ Real.log (1 + (23740009868623 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23740009868623 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-14551028044479 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (86132183787158 / 231980123821523 : ℝ) ≤ (177757590684793 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (43066091893579 / 50000000000000 : ℝ) ≤ (177757590684793 / 250000000000000 : ℝ) := by
    have hw : (131980123821523 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (43066091893579 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (43066091893579 / 50000000000000 : ℝ) / (1 + (131980123821523 / 100000000000000 : ℝ)) = (86132183787158 / 231980123821523 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85976596405572461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 43066091893579 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 43066091893579 : ℝ) = (43066091893579 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 86132183787157 : ℝ) ≤ (86856388613753 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85976596405572461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (43066091893579 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (86132183787157 / 100000000000000 : ℝ)) ≤ (86856388613753 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_641 : ∀ t : ℝ, (23740009868623 / 32000000000000 : ℝ) < t → t ≤ (1188524329359 / 1600000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-53348344530846937981847389 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (1188524329359 / 1600000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_642
  have hV : (27905505072544574460930611624968733 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23740009868623 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_641 (Vfield_monotoneOn (show (23740009868623 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23740009868623 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_642 : (2792474002632484227514062658779867 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (1188524329359 / 1600000000000 : ℝ) := by
  have hp : (0 : ℝ) < (1188524329359 / 1600000000000 : ℝ) := by norm_num
  have hs1 : (8618745302243 / 10000000000000 : ℝ) ≤ Real.sqrt (1188524329359 / 1600000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (1188524329359 / 1600000000000 : ℝ) ≤ (86187453022431 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (86187453022431 / 100000000000000 : ℝ) = (100000000000000 / 86187453022431 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8618745302243 / 10000000000000 : ℝ) = (750000000000 / 8618745302243 : ℝ) := by norm_num
  have hL1 : (27775445622741 / 50000000000000 : ℝ) ≤ Real.log (1 + (1188524329359 / 1600000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((1188524329359 / 1600000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1158989048387 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (9576383669159 / 25779577776117 : ℝ) ≤ (355673786674079 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (86187453022431 / 100000000000000 : ℝ) ≤ (355673786674079 / 500000000000000 : ℝ) := by
    have hw : (132016199985053 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (86187453022431 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (86187453022431 / 100000000000000 : ℝ) / (1 + (132016199985053 / 100000000000000 : ℝ)) = (9576383669159 / 25779577776117 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85944875344673861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 86187453022431 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 86187453022431 : ℝ) = (86187453022431 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 8618745302243 : ℝ) ≤ (86800969847947 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85944875344673861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (86187453022431 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8618745302243 / 10000000000000 : ℝ)) ≤ (86800969847947 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_642 : ∀ t : ℝ, (1188524329359 / 1600000000000 : ℝ) < t → t ≤ (23800963305737 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-26584266391250005908207001 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (23800963305737 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_643
  have hV : (2792474002632484227514062658779867 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (1188524329359 / 1600000000000 : ℝ) := by norm_num
    refine le_trans V_pt_642 (Vfield_monotoneOn (show (1188524329359 / 1600000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (1188524329359 / 1600000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_643 : (27943962737054302553848558841780839 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (23800963305737 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (23800963305737 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (86242686838031 / 100000000000000 : ℝ) ≤ Real.sqrt (23800963305737 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (23800963305737 / 32000000000000 : ℝ) ≤ (5390167927377 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5390167927377 / 6250000000000 : ℝ) = (6250000000000 / 5390167927377 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (86242686838031 / 100000000000000 : ℝ) = (7500000000000 / 86242686838031 : ℝ) := by norm_num
  have hL1 : (55605522998219 / 100000000000000 : ℝ) ≤ Real.log (1 + (23800963305737 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((23800963305737 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1442377912661 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (86242686838032 / 232052266292717 : ℝ) ≤ (14233288149677 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5390167927377 / 6250000000000 : ℝ) ≤ (14233288149677 / 20000000000000 : ℝ) := by
    have hw : (132052266292717 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (5390167927377 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (5390167927377 / 6250000000000 : ℝ) / (1 + (132052266292717 / 100000000000000 : ℝ)) = (86242686838032 / 232052266292717 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85913191931104661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 5390167927377 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 5390167927377 : ℝ) = (5390167927377 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 86242686838031 : ℝ) ≤ (86745657027407 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85913191931104661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5390167927377 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (86242686838031 / 100000000000000 : ℝ)) ≤ (86745657027407 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_643 : ∀ t : ℝ, (23800963305737 / 32000000000000 : ℝ) < t → t ≤ (11915720012147 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-827960645997125472864193 / 1562500000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (11915720012147 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_644
  have hV : (27943962737054302553848558841780839 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (23800963305737 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_643 (Vfield_monotoneOn (show (23800963305737 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (23800963305737 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_644 : (27963173226866805040577500084279161 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (11915720012147 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (11915720012147 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (86297885301969 / 100000000000000 : ℝ) ≤ Real.sqrt (11915720012147 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (11915720012147 / 16000000000000 : ℝ) ≤ (8629788530197 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8629788530197 / 10000000000000 : ℝ) = (10000000000000 / 8629788530197 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (86297885301969 / 100000000000000 : ℝ) = (2500000000000 / 28765961767323 : ℝ) := by norm_num
  have hL1 : (55660124920967 / 100000000000000 : ℝ) ≤ Real.log (1 + (11915720012147 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((11915720012147 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-14360275904143 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (43148942650985 / 116044161376294 : ℝ) ≤ (177995216486819 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8629788530197 / 10000000000000 : ℝ) ≤ (177995216486819 / 250000000000000 : ℝ) := by
    have hw : (33022080688147 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (8629788530197 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8629788530197 / 10000000000000 : ℝ) / (1 + (33022080688147 / 25000000000000 : ℝ)) = (43148942650985 / 116044161376294 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85881546084762061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 8629788530197 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 8629788530197 : ℝ) = (8629788530197 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 28765961767323 : ℝ) ≤ (17338089963 / 200000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85881546084762061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8629788530197 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (86297885301969 / 100000000000000 : ℝ)) ≤ (17338089963 / 200000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_644 : ∀ t : ℝ, (11915720012147 / 16000000000000 : ℝ) < t → t ≤ (746637295669 / 1000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-13158393979419221713642131 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (746637295669 / 1000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_645
  have hV : (27963173226866805040577500084279161 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (11915720012147 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_644 (Vfield_monotoneOn (show (11915720012147 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (11915720012147 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_645 : (1750097351996826374513352391481647 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (746637295669 / 1000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (746637295669 / 1000000000000 : ℝ) := by norm_num
  have hs1 : (5400511027863 / 6250000000000 : ℝ) ≤ Real.sqrt (746637295669 / 1000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (746637295669 / 1000000000000 : ℝ) ≤ (86408176445809 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (86408176445809 / 100000000000000 : ℝ) = (100000000000000 / 86408176445809 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5400511027863 / 6250000000000 : ℝ) = (156250000000 / 1800170342621 : ℝ) := by norm_num
  have hL1 : (55769239406677 / 100000000000000 : ℝ) ≤ Real.log (1 + (746637295669 / 1000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((746637295669 / 1000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5693404363117 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (86408176445809 / 232160406161187 : ℝ) ≤ (356306329524337 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (86408176445809 / 100000000000000 : ℝ) ≤ (356306329524337 / 500000000000000 : ℝ) := by
    have hw : (132160406161187 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (86408176445809 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (86408176445809 / 100000000000000 : ℝ) / (1 + (132160406161187 / 100000000000000 : ℝ)) = (86408176445809 / 232160406161187 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85818366774622261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 86408176445809 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 86408176445809 : ℝ) = (86408176445809 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (156250000000 / 1800170342621 : ℝ) ≤ (86580350873531 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85818366774622261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (86408176445809 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5400511027863 / 6250000000000 : ℝ)) ≤ (86580350873531 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_645 : ∀ t : ℝ, (746637295669 / 1000000000000 : ℝ) < t → t ≤ (765809953469387 / 1024000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-52358117890121635401232091 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (765809953469387 / 1024000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_646
  have hV : (1750097351996826374513352391481647 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (746637295669 / 1000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_645 (Vfield_monotoneOn (show (746637295669 / 1000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (746637295669 / 1000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_646 : (1751637318232066620668600399799777 / 312500000000000000000000000000000 : ℝ) ≤ Vfield (765809953469387 / 1024000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (765809953469387 / 1024000000000000 : ℝ) := by norm_num
  have hs1 : (5404935832633 / 6250000000000 : ℝ) ≤ Real.sqrt (765809953469387 / 1024000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (765809953469387 / 1024000000000000 : ℝ) ≤ (86478973322129 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (86478973322129 / 100000000000000 : ℝ) = (100000000000000 / 86478973322129 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (5404935832633 / 6250000000000 : ℝ) = (468750000000 / 5404935832633 : ℝ) := by norm_num
  have hL1 : (55839291635261 / 100000000000000 : ℝ) ≤ Real.log (1 + (765809953469387 / 1024000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((765809953469387 / 1024000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-28304446561903 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (86478973322129 / 232206704923954 : ℝ) ≤ (178254462389013 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (86478973322129 / 100000000000000 : ℝ) ≤ (178254462389013 / 250000000000000 : ℝ) := by
    have hw : (66103352461977 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (86478973322129 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (86478973322129 / 100000000000000 : ℝ) / (1 + (66103352461977 / 50000000000000 : ℝ)) = (86478973322129 / 232206704923954 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85777847723884461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 86478973322129 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 86478973322129 : ℝ) = (86478973322129 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (468750000000 / 5404935832633 : ℝ) ≤ (86509824258943 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85777847723884461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (86478973322129 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (5404935832633 / 6250000000000 : ℝ)) ≤ (86509824258943 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_646 : ∀ t : ℝ, (765809953469387 / 1024000000000000 : ℝ) < t → t ≤ (383531658086859 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-13028015841294940627690393 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (383531658086859 / 512000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_647
  have hV : (1751637318232066620668600399799777 / 312500000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (765809953469387 / 1024000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_646 (Vfield_monotoneOn (show (765809953469387 / 1024000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (765809953469387 / 1024000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_647 : (7012704130566073269512894668172273 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (383531658086859 / 512000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (383531658086859 / 512000000000000 : ℝ) := by norm_num
  have hs1 : (21637428071817 / 25000000000000 : ℝ) ≤ Real.sqrt (383531658086859 / 512000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (383531658086859 / 512000000000000 : ℝ) ≤ (86549712287269 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (86549712287269 / 100000000000000 : ℝ) = (100000000000000 / 86549712287269 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21637428071817 / 25000000000000 : ℝ) = (625000000000 / 7212476023939 : ℝ) := by norm_num
  have hL1 : (1118185896501 / 2000000000000 : ℝ) ≤ Real.log (1 + (383531658086859 / 512000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((383531658086859 / 512000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-28142135186409 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (7868155662479 / 21113907952598 : ℝ) ≤ (356711212603543 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (86549712287269 / 100000000000000 : ℝ) ≤ (356711212603543 / 500000000000000 : ℝ) := by
    have hw : (66126493739289 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (86549712287269 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (86549712287269 / 100000000000000 : ℝ) / (1 + (66126493739289 / 50000000000000 : ℝ)) = (7868155662479 / 21113907952598 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85737390158781061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 86549712287269 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 86549712287269 : ℝ) = (86549712287269 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (625000000000 / 7212476023939 : ℝ) ≤ (86439469713593 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85737390158781061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (86549712287269 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21637428071817 / 25000000000000 : ℝ)) ≤ (86439469713593 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_647 : ∀ t : ℝ, (383531658086859 / 512000000000000 : ℝ) < t → t ≤ (768316678878049 / 1024000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1620992355279273346368857 / 3125000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (768316678878049 / 1024000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_648
  have hV : (7012704130566073269512894668172273 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (383531658086859 / 512000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_647 (Vfield_monotoneOn (show (383531658086859 / 512000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (383531658086859 / 512000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_648 : (28075415969833235533344546946104283 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (768316678878049 / 1024000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (768316678878049 / 1024000000000000 : ℝ) := by norm_num
  have hs1 : (86620393483107 / 100000000000000 : ℝ) ≤ Real.sqrt (768316678878049 / 1024000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (768316678878049 / 1024000000000000 : ℝ) ≤ (21655098370777 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21655098370777 / 25000000000000 : ℝ) = (25000000000000 / 21655098370777 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (86620393483107 / 100000000000000 : ℝ) = (2500000000000 / 28873464494369 : ℝ) := by norm_num
  have hL1 : (55979249044651 / 100000000000000 : ℝ) ≤ Real.log (1 + (768316678878049 / 1024000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((768316678878049 / 1024000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-13990043416941 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (86620393483108 / 232299253842069 : ℝ) ≤ (356913193836443 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21655098370777 / 25000000000000 : ℝ) ≤ (356913193836443 / 500000000000000 : ℝ) := by
    have hw : (132299253842069 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (21655098370777 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (21655098370777 / 25000000000000 : ℝ) / (1 + (132299253842069 / 100000000000000 : ℝ)) = (86620393483108 / 232299253842069 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85696993912201061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 21655098370777 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 21655098370777 : ℝ) = (21655098370777 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 28873464494369 : ℝ) ≤ (86369286538933 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85696993912201061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21655098370777 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (86620393483107 / 100000000000000 : ℝ)) ≤ (86369286538933 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_648 : ∀ t : ℝ, (768316678878049 / 1024000000000000 : ℝ) < t → t ≤ (38478502079119 / 51200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-51634918102225873037722839 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (38478502079119 / 51200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_649
  have hV : (28075415969833235533344546946104283 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (768316678878049 / 1024000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_648 (Vfield_monotoneOn (show (768316678878049 / 1024000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (768316678878049 / 1024000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_649 : (7024998870118942512527808813389753 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (38478502079119 / 51200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (38478502079119 / 51200000000000 : ℝ) := by norm_num
  have hs1 : (21672754262737 / 25000000000000 : ℝ) ≤ Real.sqrt (38478502079119 / 51200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (38478502079119 / 51200000000000 : ℝ) ≤ (86691017050949 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (86691017050949 / 100000000000000 : ℝ) = (100000000000000 / 86691017050949 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21672754262737 / 25000000000000 : ℝ) = (1875000000000 / 21672754262737 : ℝ) := by norm_num
  have hL1 : (56049154362531 / 100000000000000 : ℝ) ≤ Real.log (1 + (38478502079119 / 51200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((38478502079119 / 51200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-13909150326627 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (86691017050949 / 232345504031409 : ℝ) ≤ (357114869308887 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (86691017050949 / 100000000000000 : ℝ) ≤ (357114869308887 / 500000000000000 : ℝ) := by
    have hw : (132345504031409 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (86691017050949 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (86691017050949 / 100000000000000 : ℝ) / (1 + (132345504031409 / 100000000000000 : ℝ)) = (86691017050949 / 232345504031409 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85656658817712261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 86691017050949 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 86691017050949 : ℝ) = (86691017050949 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 21672754262737 : ℝ) ≤ (43149637020187 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85656658817712261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (86691017050949 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21672754262737 / 25000000000000 : ℝ)) ≤ (43149637020187 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_649 : ∀ t : ℝ, (38478502079119 / 51200000000000 : ℝ) < t → t ≤ (770823404286711 / 1024000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-5140065314440841751066167 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (770823404286711 / 1024000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_650
  have hV : (7024998870118942512527808813389753 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (38478502079119 / 51200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_649 (Vfield_monotoneOn (show (38478502079119 / 51200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (38478502079119 / 51200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_650 : (14062277550036367414143796580083671 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (770823404286711 / 1024000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (770823404286711 / 1024000000000000 : ℝ) := by norm_num
  have hs1 : (43380791565759 / 50000000000000 : ℝ) ≤ Real.sqrt (770823404286711 / 1024000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (770823404286711 / 1024000000000000 : ℝ) ≤ (86761583131519 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (86761583131519 / 100000000000000 : ℝ) = (100000000000000 / 86761583131519 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (43380791565759 / 50000000000000 : ℝ) = (1250000000000 / 14460263855253 : ℝ) := by norm_num
  have hL1 : (56119010847011 / 100000000000000 : ℝ) ≤ Real.log (1 + (770823404286711 / 1024000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((770823404286711 / 1024000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-27656775797577 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (86761583131519 / 232391738063549 : ℝ) ≤ (89329059962411 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (86761583131519 / 100000000000000 : ℝ) ≤ (89329059962411 / 125000000000000 : ℝ) := by
    have hw : (132391738063549 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (86761583131519 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (86761583131519 / 100000000000000 : ℝ) / (1 + (132391738063549 / 100000000000000 : ℝ)) = (86761583131519 / 232391738063549 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85616384709560861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 86761583131519 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 86761583131519 : ℝ) = (86761583131519 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 14460263855253 : ℝ) ≤ (86229431527261 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85616384709560861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (86761583131519 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (43380791565759 / 50000000000000 : ℝ)) ≤ (86229431527261 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_650 : ∀ t : ℝ, (770823404286711 / 1024000000000000 : ℝ) < t → t ≤ (386038383495521 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-319803047918445705656613 / 625000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (386038383495521 / 512000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_651
  have hV : (14062277550036367414143796580083671 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (770823404286711 / 1024000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_650 (Vfield_monotoneOn (show (770823404286711 / 1024000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (770823404286711 / 1024000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_651 : (28149094874330618536259251554597699 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (386038383495521 / 512000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (386038383495521 / 512000000000000 : ℝ) := by norm_num
  have hs1 : (86832091864971 / 100000000000000 : ℝ) ≤ Real.sqrt (386038383495521 / 512000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (386038383495521 / 512000000000000 : ℝ) ≤ (21708022966243 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (21708022966243 / 25000000000000 : ℝ) = (25000000000000 / 21708022966243 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (86832091864971 / 100000000000000 : ℝ) = (2500000000000 / 28944030621657 : ℝ) := by norm_num
  have hL1 : (5618881856627 / 10000000000000 : ℝ) ≤ Real.log (1 + (386038383495521 / 512000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((386038383495521 / 512000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-27495511424003 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (86832091864972 / 232437955955409 : ℝ) ≤ (8937932657103 / 25000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (21708022966243 / 25000000000000 : ℝ) ≤ (8937932657103 / 12500000000000 : ℝ) := by
    have hw : (132437955955409 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (21708022966243 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (21708022966243 / 25000000000000 : ℝ) / (1 + (132437955955409 / 100000000000000 : ℝ)) = (86832091864972 / 232437955955409 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85576171422665661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 21708022966243 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 21708022966243 : ℝ) = (21708022966243 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 28944030621657 : ℝ) ≤ (1723195166257 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85576171422665661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (21708022966243 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (86832091864971 / 100000000000000 : ℝ)) ≤ (1723195166257 / 20000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_651 : ∀ t : ℝ, (386038383495521 / 512000000000000 : ℝ) < t → t ≤ (773330129695373 / 1024000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-25469065847224218030439453 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (773330129695373 / 1024000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_652
  have hV : (28149094874330618536259251554597699 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (386038383495521 / 512000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_651 (Vfield_monotoneOn (show (386038383495521 / 512000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (386038383495521 / 512000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_652 : (14086807424391925326522092359093743 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (773330129695373 / 1024000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (773330129695373 / 1024000000000000 : ℝ) := by norm_num
  have hs1 : (43451271695447 / 50000000000000 : ℝ) ≤ Real.sqrt (773330129695373 / 1024000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (773330129695373 / 1024000000000000 : ℝ) ≤ (17380508678179 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17380508678179 / 20000000000000 : ℝ) = (20000000000000 / 17380508678179 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (43451271695447 / 50000000000000 : ℝ) = (3750000000000 / 43451271695447 : ℝ) := by norm_num
  have hL1 : (28129288794173 / 50000000000000 : ℝ) ≤ Real.log (1 + (773330129695373 / 1024000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((773330129695373 / 1024000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5466901338751 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (86902543390895 / 232484157723881 : ℝ) ≤ (178859034717187 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17380508678179 / 20000000000000 : ℝ) ≤ (178859034717187 / 250000000000000 : ℝ) := by
    have hw : (132484157723881 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (17380508678179 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17380508678179 / 20000000000000 : ℝ) / (1 + (132484157723881 / 100000000000000 : ℝ)) = (86902543390895 / 232484157723881 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85536018792614861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 17380508678179 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 17380508678179 : ℝ) = (17380508678179 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 43451271695447 : ℝ) ≤ (2690320428571 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85536018792614861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17380508678179 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (43451271695447 / 50000000000000 : ℝ)) ≤ (2690320428571 / 31250000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_652 : ∀ t : ℝ, (773330129695373 / 1024000000000000 : ℝ) < t → t ≤ (96822936549963 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2028375567638438735952231 / 4000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (96822936549963 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_653
  have hV : (14086807424391925326522092359093743 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (773330129695373 / 1024000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_652 (Vfield_monotoneOn (show (773330129695373 / 1024000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (773330129695373 / 1024000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_653 : (28198115068794868634068286813714621 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (96822936549963 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (96822936549963 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (86972937848309 / 100000000000000 : ℝ) ≤ Real.sqrt (96822936549963 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (96822936549963 / 128000000000000 : ℝ) ≤ (8697293784831 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8697293784831 / 10000000000000 : ℝ) = (10000000000000 / 8697293784831 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (86972937848309 / 100000000000000 : ℝ) = (7500000000000 / 86972937848309 : ℝ) := by norm_num
  have hL1 : (56328287981131 / 100000000000000 : ℝ) ≤ Real.log (1 + (96822936549963 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((96822936549963 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-27173760772101 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (28990979282770 / 77510114461943 : ℝ) ≤ (11184954066223 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8697293784831 / 10000000000000 : ℝ) ≤ (11184954066223 / 15625000000000 : ℝ) := by
    have hw : (132530343385829 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (8697293784831 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8697293784831 / 10000000000000 : ℝ) / (1 + (132530343385829 / 100000000000000 : ℝ)) = (28990979282770 / 77510114461943 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85495926655662461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 8697293784831 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 8697293784831 : ℝ) = (8697293784831 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 86972937848309 : ℝ) ≤ (21505229263127 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85495926655662461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8697293784831 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (86972937848309 / 100000000000000 : ℝ)) ≤ (21505229263127 / 250000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_653 : ∀ t : ℝ, (96822936549963 / 128000000000000 : ℝ) < t → t ≤ (155167371020807 / 204800000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-50482118300246065456819321 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (155167371020807 / 204800000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_654
  have hV : (28198115068794868634068286813714621 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (96822936549963 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_653 (Vfield_monotoneOn (show (96822936549963 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (96822936549963 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_654 : (28222595579554294985023060221997537 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (155167371020807 / 204800000000000 : ℝ) := by
  have hp : (0 : ℝ) < (155167371020807 / 204800000000000 : ℝ) := by norm_num
  have hs1 : (87043275375673 / 100000000000000 : ℝ) ≤ Real.sqrt (155167371020807 / 204800000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (155167371020807 / 204800000000000 : ℝ) ≤ (43521637687837 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (43521637687837 / 50000000000000 : ℝ) = (50000000000000 / 43521637687837 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (87043275375673 / 100000000000000 : ℝ) = (7500000000000 / 87043275375673 : ℝ) := by norm_num
  have hL1 : (28198974906189 / 50000000000000 : ℝ) ≤ Real.log (1 + (155167371020807 / 204800000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((155167371020807 / 204800000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-13506636414163 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (87043275375674 / 232576512958085 : ℝ) ≤ (358118689153817 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (43521637687837 / 50000000000000 : ℝ) ≤ (358118689153817 / 500000000000000 : ℝ) := by
    have hw : (26515302591617 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (43521637687837 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (43521637687837 / 50000000000000 : ℝ) / (1 + (26515302591617 / 20000000000000 : ℝ)) = (87043275375674 / 232576512958085 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85455894848726261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 43521637687837 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 43521637687837 : ℝ) = (43521637687837 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 87043275375673 : ℝ) ≤ (42975873826181 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85455894848726261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (43521637687837 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (87043275375673 / 100000000000000 : ℝ)) ≤ (42975873826181 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_654 : ∀ t : ℝ, (155167371020807 / 204800000000000 : ℝ) < t → t ≤ (388545108904183 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-25128105543812811403986699 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (388545108904183 / 512000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_655
  have hV : (28222595579554294985023060221997537 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (155167371020807 / 204800000000000 : ℝ) := by norm_num
    refine le_trans V_pt_654 (Vfield_monotoneOn (show (155167371020807 / 204800000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (155167371020807 / 204800000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_655 : (28247056426083549047328308350367103 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (388545108904183 / 512000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (388545108904183 / 512000000000000 : ℝ) := by norm_num
  have hs1 : (87113556110887 / 100000000000000 : ℝ) ≤ Real.sqrt (388545108904183 / 512000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (388545108904183 / 512000000000000 : ℝ) ≤ (10889194513861 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (10889194513861 / 12500000000000 : ℝ) = (12500000000000 / 10889194513861 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (87113556110887 / 100000000000000 : ℝ) = (7500000000000 / 87113556110887 : ℝ) := by norm_num
  have hL1 : (56467563149697 / 100000000000000 : ℝ) ≤ Real.log (1 + (388545108904183 / 512000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((388545108904183 / 512000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-26853042035711 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (87113556110888 / 232622666457453 : ℝ) ≤ (179159273675273 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (10889194513861 / 12500000000000 : ℝ) ≤ (179159273675273 / 250000000000000 : ℝ) := by
    have hw : (132622666457453 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (10889194513861 / 12500000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (10889194513861 / 12500000000000 : ℝ) / (1 + (132622666457453 / 100000000000000 : ℝ)) = (87113556110888 / 232622666457453 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85415923209380461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 10889194513861 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (12500000000000 / 10889194513861 : ℝ) = (10889194513861 / 12500000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 87113556110887 : ℝ) ≤ (85882744842431 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85415923209380461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (10889194513861 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (87113556110887 / 100000000000000 : ℝ)) ≤ (85882744842431 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_655 : ∀ t : ℝ, (388545108904183 / 512000000000000 : ℝ) < t → t ≤ (194899235804257 / 256000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-79693059371923046646177 / 160000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (194899235804257 / 256000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_656
  have hV : (28247056426083549047328308350367103 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (388545108904183 / 512000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_655 (Vfield_monotoneOn (show (388545108904183 / 512000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (388545108904183 / 512000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_656 : (2829591930569078791167475401323761 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (194899235804257 / 256000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (194899235804257 / 256000000000000 : ℝ) := by norm_num
  have hs1 : (8725394775369 / 10000000000000 : ℝ) ≤ Real.sqrt (194899235804257 / 256000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (194899235804257 / 256000000000000 : ℝ) ≤ (87253947753691 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (87253947753691 / 100000000000000 : ℝ) = (100000000000000 / 87253947753691 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (8725394775369 / 10000000000000 : ℝ) = (250000000000 / 2908464925123 : ℝ) := by norm_num
  have hL1 : (56606644612291 / 100000000000000 : ℝ) ≤ Real.log (1 + (194899235804257 / 256000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((194899235804257 / 256000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2653334861689 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (87253947753691 / 232714925304593 : ℝ) ≤ (71743472892461 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (87253947753691 / 100000000000000 : ℝ) ≤ (71743472892461 / 100000000000000 : ℝ) := by
    have hw : (132714925304593 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (87253947753691 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (87253947753691 / 100000000000000 : ℝ) / (1 + (132714925304593 / 100000000000000 : ℝ)) = (87253947753691 / 232714925304593 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85336159787028661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 87253947753691 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 87253947753691 : ℝ) = (87253947753691 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (250000000000 / 2908464925123 : ℝ) ≤ (5359077270401 / 62500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85336159787028661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (87253947753691 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (8725394775369 / 10000000000000 : ℝ)) ≤ (5359077270401 / 62500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_656 : ∀ t : ℝ, (194899235804257 / 256000000000000 : ℝ) < t → t ≤ (78210366862569 / 102400000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-49364724513564176241161649 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (78210366862569 / 102400000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_657
  have hV : (2829591930569078791167475401323761 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (194899235804257 / 256000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_656 (Vfield_monotoneOn (show (194899235804257 / 256000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (194899235804257 / 256000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_657 : (28344704064416540399110227366496033 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (78210366862569 / 102400000000000 : ℝ) := by
  have hp : (0 : ℝ) < (78210366862569 / 102400000000000 : ℝ) := by norm_num
  have hs1 : (87394113868857 / 100000000000000 : ℝ) ≤ Real.sqrt (78210366862569 / 102400000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (78210366862569 / 102400000000000 : ℝ) ≤ (43697056934429 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (43697056934429 / 50000000000000 : ℝ) = (50000000000000 / 43697056934429 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (87394113868857 / 100000000000000 : ℝ) = (2500000000000 / 29131371289619 : ℝ) := by norm_num
  have hL1 : (56745532906981 / 100000000000000 : ℝ) ≤ Real.log (1 + (78210366862569 / 102400000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((78210366862569 / 102400000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-26214673980773 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (43697056934429 / 116403560030549 : ℝ) ≤ (71822997577249 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (43697056934429 / 50000000000000 : ℝ) ≤ (71822997577249 / 100000000000000 : ℝ) := by
    have hw : (66403560030549 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (43697056934429 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (43697056934429 / 50000000000000 : ℝ) / (1 + (66403560030549 / 50000000000000 : ℝ)) = (43697056934429 / 116403560030549 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85256635102240661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 43697056934429 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 43697056934429 : ℝ) = (43697056934429 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (2500000000000 / 29131371289619 : ℝ) ≤ (85608386208099 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85256635102240661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (43697056934429 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (87394113868857 / 100000000000000 : ℝ)) ≤ (85608386208099 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_657 : ∀ t : ℝ, (78210366862569 / 102400000000000 : ℝ) < t → t ≤ (49038149627147 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-12231381416271381650614621 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (49038149627147 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_658
  have hV : (28344704064416540399110227366496033 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (78210366862569 / 102400000000000 : ℝ) := by norm_num
    refine le_trans V_pt_657 (Vfield_monotoneOn (show (78210366862569 / 102400000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (78210366862569 / 102400000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_658 : (14196705528197497723690889758681179 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (49038149627147 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (49038149627147 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (43767027769891 / 50000000000000 : ℝ) ≤ Real.sqrt (49038149627147 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (49038149627147 / 64000000000000 : ℝ) ≤ (87534055539783 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (87534055539783 / 100000000000000 : ℝ) = (100000000000000 / 87534055539783 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (43767027769891 / 50000000000000 : ℝ) = (3750000000000 / 43767027769891 : ℝ) := by norm_num
  have hL1 : (56884228569601 / 100000000000000 : ℝ) ≤ Real.log (1 + (49038149627147 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((49038149627147 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6474252913693 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (29178018513261 / 77633083620116 : ℝ) ≤ (35951142400267 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (87534055539783 / 100000000000000 : ℝ) ≤ (35951142400267 / 50000000000000 : ℝ) := by
    have hw : (33224812715087 / 25000000000000 : ℝ) ≤ Real.sqrt (1 + (87534055539783 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (87534055539783 / 100000000000000 : ℝ) / (1 + (33224812715087 / 25000000000000 : ℝ)) = (29178018513261 / 77633083620116 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85177347878955661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 87534055539783 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 87534055539783 : ℝ) = (87534055539783 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 43767027769891 : ℝ) ≤ (17094437850021 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85177347878955661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (87534055539783 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (43767027769891 / 50000000000000 : ℝ)) ≤ (17094437850021 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_658 : ∀ t : ℝ, (49038149627147 / 64000000000000 : ℝ) < t → t ≤ (393558559721507 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-24245139860676967208844121 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (393558559721507 / 512000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_659
  have hV : (14196705528197497723690889758681179 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (49038149627147 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_658 (Vfield_monotoneOn (show (49038149627147 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (49038149627147 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_659 : (5688408126624673141206981722733867 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (393558559721507 / 512000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (393558559721507 / 512000000000000 : ℝ) := by norm_num
  have hs1 : (17534754768243 / 20000000000000 : ℝ) ≤ Real.sqrt (393558559721507 / 512000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (393558559721507 / 512000000000000 : ℝ) ≤ (1369902716269 / 1562500000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1369902716269 / 1562500000000 : ℝ) = (1562500000000 / 1369902716269 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17534754768243 / 20000000000000 : ℝ) = (500000000000 / 5844918256081 : ℝ) := by norm_num
  have hL1 : (57022732133753 / 100000000000000 : ℝ) ≤ Real.log (1 + (393558559721507 / 512000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((393558559721507 / 512000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5116071045557 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (87673773841216 / 232991317835265 : ℝ) ≤ (179953339570459 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (1369902716269 / 1562500000000 : ℝ) ≤ (179953339570459 / 250000000000000 : ℝ) := by
    have hw : (26598263567053 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (1369902716269 / 1562500000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (1369902716269 / 1562500000000 : ℝ) / (1 + (26598263567053 / 20000000000000 : ℝ)) = (87673773841216 / 232991317835265 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85098296851306061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1562500000000 / 1369902716269 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (1562500000000 / 1369902716269 : ℝ) = (1369902716269 / 1562500000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (500000000000 / 5844918256081 : ℝ) ≤ (85336640273197 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85098296851306061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (1369902716269 / 1562500000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17534754768243 / 20000000000000 : ℝ)) ≤ (85336640273197 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_659 : ∀ t : ℝ, (393558559721507 / 512000000000000 : ℝ) < t → t ≤ (197405961212919 / 256000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-48058757364746658548766453 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (197405961212919 / 256000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_660
  have hV : (5688408126624673141206981722733867 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (393558559721507 / 512000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_659 (Vfield_monotoneOn (show (393558559721507 / 512000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (393558559721507 / 512000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_660 : (7122648285872267905531839227631191 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (197405961212919 / 256000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (197405961212919 / 256000000000000 : ℝ) := by norm_num
  have hs1 : (21953317459839 / 25000000000000 : ℝ) ≤ Real.sqrt (197405961212919 / 256000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (197405961212919 / 256000000000000 : ℝ) ≤ (87813269839357 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (87813269839357 / 100000000000000 : ℝ) = (100000000000000 / 87813269839357 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21953317459839 / 25000000000000 : ℝ) = (625000000000 / 7317772486613 : ℝ) := by norm_num
  have hL1 : (57161044130829 / 100000000000000 : ℝ) ≤ Real.log (1 + (197405961212919 / 256000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((197405961212919 / 256000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-25264698349423 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (87813269839357 / 233083321118311 : ℝ) ≤ (90075189894977 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (87813269839357 / 100000000000000 : ℝ) ≤ (90075189894977 / 125000000000000 : ℝ) := by
    have hw : (133083321118311 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (87813269839357 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (87813269839357 / 100000000000000 : ℝ) / (1 + (133083321118311 / 100000000000000 : ℝ)) = (87813269839357 / 233083321118311 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (85019480763508061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 87813269839357 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 87813269839357 : ℝ) = (87813269839357 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (625000000000 / 7317772486613 : ℝ) ≤ (1704034683109 / 20000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (85019480763508061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (87813269839357 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21953317459839 / 25000000000000 : ℝ)) ≤ (1704034683109 / 20000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_660 : ∀ t : ℝ, (197405961212919 / 256000000000000 : ℝ) < t → t ≤ (396065285130169 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-952615369553781229432851 / 2000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (396065285130169 / 512000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_661
  have hV : (7122648285872267905531839227631191 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (197405961212919 / 256000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_660 (Vfield_monotoneOn (show (197405961212919 / 256000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (197405961212919 / 256000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_661 : (7134767233448823605206799856397003 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (396065285130169 / 512000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (396065285130169 / 512000000000000 : ℝ) := by norm_num
  have hs1 : (21988136147987 / 25000000000000 : ℝ) ≤ Real.sqrt (396065285130169 / 512000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (396065285130169 / 512000000000000 : ℝ) ≤ (87952544591949 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (87952544591949 / 100000000000000 : ℝ) = (100000000000000 / 87952544591949 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (21988136147987 / 25000000000000 : ℝ) = (1875000000000 / 21988136147987 : ℝ) := by norm_num
  have hL1 : (28649582545009 / 50000000000000 : ℝ) ≤ Real.log (1 + (396065285130169 / 512000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((396065285130169 / 512000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4990006945849 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (9772504954661 / 25908362315721 : ℝ) ≤ (72138734309737 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (87952544591949 / 100000000000000 : ℝ) ≤ (72138734309737 / 100000000000000 : ℝ) := by
    have hw : (133175260841489 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (87952544591949 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (87952544591949 / 100000000000000 : ℝ) / (1 + (133175260841489 / 100000000000000 : ℝ)) = (9772504954661 / 25908362315721 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (84940898369752661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 87952544591949 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 87952544591949 : ℝ) = (87952544591949 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 21988136147987 : ℝ) ≤ (10633433228931 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (84940898369752661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (87952544591949 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (21988136147987 / 25000000000000 : ℝ)) ≤ (10633433228931 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_661 : ∀ t : ℝ, (396065285130169 / 512000000000000 : ℝ) < t → t ≤ (794637295669 / 1024000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23603075737768115877860651 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (794637295669 / 1024000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_662
  have hV : (7134767233448823605206799856397003 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (396065285130169 / 512000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_661 (Vfield_monotoneOn (show (396065285130169 / 512000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (396065285130169 / 512000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_662 : (7146867086947150332249666404479517 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (794637295669 / 1024000000000 : ℝ) := by
  have hp : (0 : ℝ) < (794637295669 / 1024000000000 : ℝ) := by norm_num
  have hs1 : (22022899787093 / 25000000000000 : ℝ) ≤ Real.sqrt (794637295669 / 1024000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (794637295669 / 1024000000000 : ℝ) ≤ (88091599148373 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (88091599148373 / 100000000000000 : ℝ) = (100000000000000 / 88091599148373 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (22022899787093 / 25000000000000 : ℝ) = (1875000000000 / 22022899787093 : ℝ) := by norm_num
  have hL1 : (57437095538319 / 100000000000000 : ℝ) ≤ Real.log (1 + (794637295669 / 1024000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((794637295669 / 1024000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-12318179068001 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (88091599148373 / 233267137136345 : ℝ) ≤ (180542710613481 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (88091599148373 / 100000000000000 : ℝ) ≤ (180542710613481 / 250000000000000 : ℝ) := by
    have hw : (26653427427269 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (88091599148373 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (88091599148373 / 100000000000000 : ℝ) / (1 + (26653427427269 / 20000000000000 : ℝ)) = (88091599148373 / 233267137136345 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (84862548434097261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 88091599148373 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 88091599148373 : ℝ) = (88091599148373 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 22022899787093 : ℝ) ≤ (42466915145737 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (84862548434097261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (88091599148373 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (22022899787093 / 25000000000000 : ℝ)) ≤ (42466915145737 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_662 : ∀ t : ℝ, (794637295669 / 1024000000000 : ℝ) < t → t ≤ (398572010538831 / 512000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23392383173956301542278211 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (398572010538831 / 512000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_663
  have hV : (7146867086947150332249666404479517 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (794637295669 / 1024000000000 : ℝ) := by norm_num
    refine le_trans V_pt_662 (Vfield_monotoneOn (show (794637295669 / 1024000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (794637295669 / 1024000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_663 : (28635791726686353537952404468407367 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (398572010538831 / 512000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (398572010538831 / 512000000000000 : ℝ) := by norm_num
  have hs1 : (88230434549743 / 100000000000000 : ℝ) ≤ Real.sqrt (398572010538831 / 512000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (398572010538831 / 512000000000000 : ℝ) ≤ (5514402159359 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5514402159359 / 6250000000000 : ℝ) = (6250000000000 / 5514402159359 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (88230434549743 / 100000000000000 : ℝ) = (7500000000000 / 88230434549743 : ℝ) := by norm_num
  have hL1 : (7196854500069 / 12500000000000 : ℝ) ≤ Real.log (1 + (398572010538831 / 512000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((398572010538831 / 512000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-24323662396903 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (88230434549744 / 233358950133977 : ℝ) ≤ (180738007372829 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5514402159359 / 6250000000000 : ℝ) ≤ (180738007372829 / 250000000000000 : ℝ) := by
    have hw : (133358950133977 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (5514402159359 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (5514402159359 / 6250000000000 : ℝ) / (1 + (133358950133977 / 100000000000000 : ℝ)) = (88230434549744 / 233358950133977 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (84784429730358061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 5514402159359 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 5514402159359 : ℝ) = (5514402159359 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 88230434549743 : ℝ) ≤ (10600102822591 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (84784429730358061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5514402159359 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (88230434549743 / 100000000000000 : ℝ)) ≤ (10600102822591 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_663 : ∀ t : ℝ, (398572010538831 / 512000000000000 : ℝ) < t → t ≤ (199912686621581 / 256000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-23183244951664604685266211 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (199912686621581 / 256000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_664
  have hV : (28635791726686353537952404468407367 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (398572010538831 / 512000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_663 (Vfield_monotoneOn (show (398572010538831 / 512000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (398572010538831 / 512000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_664 : (14342019704600193724722865953593193 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (199912686621581 / 256000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (199912686621581 / 256000000000000 : ℝ) := by norm_num
  have hs1 : (44184525914497 / 50000000000000 : ℝ) ≤ Real.sqrt (199912686621581 / 256000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (199912686621581 / 256000000000000 : ℝ) ≤ (17673810365799 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (17673810365799 / 20000000000000 : ℝ) = (20000000000000 / 17673810365799 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (44184525914497 / 50000000000000 : ℝ) = (3750000000000 / 44184525914497 : ℝ) := by norm_num
  have hL1 : (28856193499687 / 50000000000000 : ℝ) ≤ Real.log (1 + (199912686621581 / 256000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((199912686621581 / 256000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-300149267461 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (29456350609665 / 77816899988342 : ℝ) ≤ (361865458187409 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (17673810365799 / 20000000000000 : ℝ) ≤ (361865458187409 / 500000000000000 : ℝ) := by
    have hw : (66725349982513 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (17673810365799 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (17673810365799 / 20000000000000 : ℝ) / (1 + (66725349982513 / 50000000000000 : ℝ)) = (29456350609665 / 77816899988342 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (84706541042007861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 17673810365799 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 17673810365799 : ℝ) = (17673810365799 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (3750000000000 / 44184525914497 : ℝ) ≤ (42334218899279 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (84706541042007861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (17673810365799 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (44184525914497 / 50000000000000 : ℝ)) ≤ (42334218899279 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_664 : ∀ t : ℝ, (199912686621581 / 256000000000000 : ℝ) < t → t ≤ (25145756165739 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-45538835037405106307363251 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (25145756165739 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_665
  have hV : (14342019704600193724722865953593193 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (199912686621581 / 256000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_664 (Vfield_monotoneOn (show (199912686621581 / 256000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (199912686621581 / 256000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_665 : (719507725688960143177776816268197 / 125000000000000000000000000000000 : ℝ) ≤ Vfield (25145756165739 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (25145756165739 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (2216140902813 / 2500000000000 : ℝ) ≤ Real.sqrt (25145756165739 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (25145756165739 / 32000000000000 : ℝ) ≤ (88645636112521 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (88645636112521 / 100000000000000 : ℝ) = (100000000000000 / 88645636112521 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (2216140902813 / 2500000000000 : ℝ) = (62500000000 / 738713634271 : ℝ) := by norm_num
  have hL1 : (7248365335831 / 12500000000000 : ℝ) ≤ Real.log (1 + (25145756165739 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((25145756165739 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-23391399438133 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (88645636112521 / 233634010647714 : ℝ) ≤ (181320459466169 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (88645636112521 / 100000000000000 : ℝ) ≤ (181320459466169 / 250000000000000 : ℝ) := by
    have hw : (66817005323857 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (88645636112521 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (88645636112521 / 100000000000000 : ℝ) / (1 + (66817005323857 / 50000000000000 : ℝ)) = (88645636112521 / 233634010647714 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (84551448893022061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 88645636112521 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 88645636112521 : ℝ) = (88645636112521 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (62500000000 / 738713634271 : ℝ) ≤ (8440551768353 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (84551448893022061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (88645636112521 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (2216140902813 / 2500000000000 : ℝ)) ≤ (8440551768353 / 100000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_665 : ∀ t : ℝ, (25145756165739 / 32000000000000 : ℝ) < t → t ≤ (202419412030243 / 256000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-44722429766736504371415607 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (202419412030243 / 256000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_666
  have hV : (719507725688960143177776816268197 / 125000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (25145756165739 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_665 (Vfield_monotoneOn (show (25145756165739 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (25145756165739 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_666 : (5775255972687761191789092378618743 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (202419412030243 / 256000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (202419412030243 / 256000000000000 : ℝ) := by norm_num
  have hs1 : (17784272020447 / 20000000000000 : ℝ) ≤ Real.sqrt (202419412030243 / 256000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (202419412030243 / 256000000000000 : ℝ) ≤ (22230340025559 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (22230340025559 / 25000000000000 : ℝ) = (25000000000000 / 22230340025559 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (17784272020447 / 20000000000000 : ℝ) = (1500000000000 / 17784272020447 : ℝ) := by norm_num
  have hL1 : (58260706738523 / 100000000000000 : ℝ) ≤ Real.log (1 + (202419412030243 / 256000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((202419412030243 / 256000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-11387342233377 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (22230340025559 / 58454267555156 : ℝ) ≤ (36341185117679 / 100000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (22230340025559 / 25000000000000 : ℝ) ≤ (36341185117679 / 50000000000000 : ℝ) := by
    have hw : (8363566888789 / 6250000000000 : ℝ) ≤ Real.sqrt (1 + (22230340025559 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (22230340025559 / 25000000000000 : ℝ) / (1 + (8363566888789 / 6250000000000 : ℝ)) = (22230340025559 / 58454267555156 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (84397262444131661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 22230340025559 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 22230340025559 : ℝ) = (22230340025559 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 17784272020447 : ℝ) ≤ (84145031795597 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (84397262444131661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (22230340025559 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (17784272020447 / 20000000000000 : ℝ)) ≤ (84145031795597 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_666 : ∀ t : ℝ, (202419412030243 / 256000000000000 : ℝ) < t → t ≤ (101836387367287 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-21958321118140792012647217 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (101836387367287 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_667
  have hV : (5775255972687761191789092378618743 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (202419412030243 / 256000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_666 (Vfield_monotoneOn (show (202419412030243 / 256000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (202419412030243 / 256000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_667 : (1158878181558027908264851810330143 / 200000000000000000000000000000000 : ℝ) ≤ Vfield (101836387367287 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (101836387367287 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (3567849271047 / 4000000000000 : ℝ) ≤ Real.sqrt (101836387367287 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (101836387367287 / 128000000000000 : ℝ) ≤ (5574764486011 / 6250000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (5574764486011 / 6250000000000 : ℝ) = (6250000000000 / 5574764486011 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (3567849271047 / 4000000000000 : ℝ) = (100000000000 / 1189283090349 : ℝ) := by norm_num
  have hL1 : (29266871629741 / 50000000000000 : ℝ) ≤ Real.log (1 + (101836387367287 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((101836387367287 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-5540437392141 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (89196231776176 / 233999879712891 : ℝ) ≤ (364178301895721 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (5574764486011 / 6250000000000 : ℝ) ≤ (364178301895721 / 500000000000000 : ℝ) := by
    have hw : (133999879712891 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (5574764486011 / 6250000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (5574764486011 / 6250000000000 : ℝ) / (1 + (133999879712891 / 100000000000000 : ℝ)) = (89196231776176 / 233999879712891 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (84243972300345461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (6250000000000 / 5574764486011 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (6250000000000 / 5574764486011 : ℝ) = (5574764486011 / 6250000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (100000000000 / 1189283090349 : ℝ) ≤ (16777388560619 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (84243972300345461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (5574764486011 / 6250000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (3567849271047 / 4000000000000 : ℝ)) ≤ (16777388560619 / 200000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_667 : ∀ t : ℝ, (101836387367287 / 128000000000000 : ℝ) < t → t ≤ (40985227487781 / 51200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-4312093229553078849049769 / 10000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (40985227487781 / 51200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_668
  have hV : (1158878181558027908264851810330143 / 200000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (101836387367287 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_667 (Vfield_monotoneOn (show (101836387367287 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (101836387367287 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_668 : (29067335638511688329033422831543501 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (40985227487781 / 51200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (40985227487781 / 51200000000000 : ℝ) := by norm_num
  have hs1 : (89470258989829 / 100000000000000 : ℝ) ≤ Real.sqrt (40985227487781 / 51200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (40985227487781 / 51200000000000 : ℝ) ≤ (8947025898983 / 10000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (8947025898983 / 10000000000000 : ℝ) = (10000000000000 / 8947025898983 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (89470258989829 / 100000000000000 : ℝ) = (7500000000000 / 89470258989829 : ℝ) := by norm_num
  have hL1 : (367537727003 / 625000000000 : ℝ) ≤ Real.log (1 + (40985227487781 / 51200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((40985227487781 / 51200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-10776274343399 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (44735129494915 / 117091220073321 : ℝ) ≤ (45617539667447 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (8947025898983 / 10000000000000 : ℝ) ≤ (45617539667447 / 62500000000000 : ℝ) := by
    have hw : (67091220073321 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (8947025898983 / 10000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (8947025898983 / 10000000000000 : ℝ) / (1 + (67091220073321 / 50000000000000 : ℝ)) = (44735129494915 / 117091220073321 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (84091569211574461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (10000000000000 / 8947025898983 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (10000000000000 / 8947025898983 : ℝ) = (8947025898983 / 10000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 89470258989829 : ℝ) ≤ (41815607085503 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (84091569211574461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (8947025898983 / 10000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (89470258989829 / 100000000000000 : ℝ)) ≤ (41815607085503 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_668 : ∀ t : ℝ, (40985227487781 / 51200000000000 : ℝ) < t → t ≤ (51544875035809 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-42334829685614189681376487 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (51544875035809 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_669
  have hV : (29067335638511688329033422831543501 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (40985227487781 / 51200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_668 (Vfield_monotoneOn (show (40985227487781 / 51200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (40985227487781 / 51200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_669 : (29162425709597596543920547511094519 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (51544875035809 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (51544875035809 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (89743449478751 / 100000000000000 : ℝ) ≤ Real.sqrt (51544875035809 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (51544875035809 / 64000000000000 : ℝ) ≤ (2804482796211 / 3125000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (2804482796211 / 3125000000000 : ℝ) = (3125000000000 / 2804482796211 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (89743449478751 / 100000000000000 : ℝ) = (7500000000000 / 89743449478751 : ℝ) := by norm_num
  have hL1 : (59077589959307 / 100000000000000 : ℝ) ≤ Real.log (1 + (51544875035809 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((51544875035809 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4189407320267 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (89743449478752 / 234364752537059 : ℝ) ≤ (365697943049403 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (2804482796211 / 3125000000000 : ℝ) ≤ (365697943049403 / 500000000000000 : ℝ) := by
    have hw : (134364752537059 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (2804482796211 / 3125000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (2804482796211 / 3125000000000 : ℝ) / (1 + (134364752537059 / 100000000000000 : ℝ)) = (89743449478752 / 234364752537059 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (83940044069609061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (3125000000000 / 2804482796211 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (3125000000000 / 2804482796211 : ℝ) = (2804482796211 / 3125000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 89743449478751 : ℝ) ≤ (41688905069621 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (83940044069609061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (2804482796211 / 3125000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (89743449478751 / 100000000000000 : ℝ)) ≤ (41688905069621 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_669 : ∀ t : ℝ, (51544875035809 / 64000000000000 : ℝ) < t → t ≤ (104343112775949 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-40789829337698339350045381 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (104343112775949 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_670
  have hV : (29162425709597596543920547511094519 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (51544875035809 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_669 (Vfield_monotoneOn (show (51544875035809 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (51544875035809 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_670 : (2935174277592522366812940832174073 / 500000000000000000000000000000000 : ℝ) ≤ Vfield (104343112775949 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (104343112775949 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (9028735064017 / 10000000000000 : ℝ) ≤ Real.sqrt (104343112775949 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (104343112775949 / 128000000000000 : ℝ) ≤ (90287350640171 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (90287350640171 / 100000000000000 : ℝ) = (100000000000000 / 90287350640171 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (9028735064017 / 10000000000000 : ℝ) = (750000000000 / 9028735064017 : ℝ) := by norm_num
  have hL1 : (3726155934871 / 6250000000000 : ℝ) ≤ Real.log (1 + (104343112775949 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((104343112775949 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9873451000907 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (90287350640171 / 234728637214295 : ℝ) ≤ (91800050993053 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (90287350640171 / 100000000000000 : ℝ) ≤ (91800050993053 / 125000000000000 : ℝ) := by
    have hw : (26945727442859 / 20000000000000 : ℝ) ≤ Real.sqrt (1 + (90287350640171 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (90287350640171 / 100000000000000 : ℝ) / (1 + (26945727442859 / 20000000000000 : ℝ)) = (90287350640171 / 234728637214295 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (83639591885047261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 90287350640171 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 90287350640171 : ℝ) = (90287350640171 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (750000000000 / 9028735064017 : ℝ) ≤ (4143891829281 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (83639591885047261923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (90287350640171 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (9028735064017 / 10000000000000 : ℝ)) ≤ (4143891829281 / 50000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_670 : ∀ t : ℝ, (104343112775949 / 128000000000000 : ℝ) < t → t ≤ (2639911887007 / 3200000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-19639401911836872200714297 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (2639911887007 / 3200000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_671
  have hV : (2935174277592522366812940832174073 / 500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (104343112775949 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_670 (Vfield_monotoneOn (show (104343112775949 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (104343112775949 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_671 : (29539925406334285778711520544618539 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (2639911887007 / 3200000000000 : ℝ) := by
  have hp : (0 : ℝ) < (2639911887007 / 3200000000000 : ℝ) := by norm_num
  have hs1 : (90827994841331 / 100000000000000 : ℝ) ≤ Real.sqrt (2639911887007 / 3200000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (2639911887007 / 3200000000000 : ℝ) ≤ (22706998710333 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (22706998710333 / 25000000000000 : ℝ) = (25000000000000 / 22706998710333 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (90827994841331 / 100000000000000 : ℝ) = (7500000000000 / 90827994841331 : ℝ) := by norm_num
  have hL1 : (60156489907931 / 100000000000000 : ℝ) ≤ Real.log (1 + (2639911887007 / 3200000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((2639911887007 / 3200000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-18560999991439 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (45413997420666 / 117545770864831 : ℝ) ≤ (73737087070983 / 200000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (22706998710333 / 25000000000000 : ℝ) ≤ (73737087070983 / 100000000000000 : ℝ) := by
    have hw : (67545770864831 / 50000000000000 : ℝ) ≤ Real.sqrt (1 + (22706998710333 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (22706998710333 / 25000000000000 : ℝ) / (1 + (67545770864831 / 50000000000000 : ℝ)) = (45413997420666 / 117545770864831 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (83342545608506661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 22706998710333 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 22706998710333 : ℝ) = (22706998710333 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 90827994841331 : ℝ) ≤ (10298343847363 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (83342545608506661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (22706998710333 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (90827994841331 / 100000000000000 : ℝ)) ≤ (10298343847363 / 125000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_671 : ∀ t : ℝ, (2639911887007 / 3200000000000 : ℝ) < t → t ≤ (106849838184611 / 128000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-7559882469674203236717089 / 20000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (106849838184611 / 128000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_672
  have hV : (29539925406334285778711520544618539 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (2639911887007 / 3200000000000 : ℝ) := by norm_num
    refine le_trans V_pt_671 (Vfield_monotoneOn (show (2639911887007 / 3200000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (2639911887007 / 3200000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_672 : (5945398544644444458866490186208833 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield (106849838184611 / 128000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (106849838184611 / 128000000000000 : ℝ) := by norm_num
  have hs1 : (18273087980057 / 20000000000000 : ℝ) ≤ Real.sqrt (106849838184611 / 128000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (106849838184611 / 128000000000000 : ℝ) ≤ (45682719950143 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (45682719950143 / 50000000000000 : ℝ) = (50000000000000 / 45682719950143 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (18273087980057 / 20000000000000 : ℝ) = (1500000000000 / 18273087980057 : ℝ) := by norm_num
  have hL1 : (60691605953717 / 100000000000000 : ℝ) ≤ Real.log (1 + (106849838184611 / 128000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((106849838184611 / 128000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-17388996949679 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (45682719950143 / 117726736980628 : ℝ) ≤ (18507698872071 / 50000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (45682719950143 / 50000000000000 : ℝ) ≤ (18507698872071 / 25000000000000 : ℝ) := by
    have hw : (16931684245157 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (45682719950143 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (45682719950143 / 50000000000000 : ℝ) / (1 + (16931684245157 / 12500000000000 : ℝ)) = (45682719950143 / 117726736980628 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (83048837191205661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 45682719950143 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 45682719950143 : ℝ) = (45682719950143 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1500000000000 / 18273087980057 : ℝ) ≤ (81904292479863 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (83048837191205661923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (45682719950143 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (18273087980057 / 20000000000000 : ℝ)) ≤ (81904292479863 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_672 : ∀ t : ℝ, (106849838184611 / 128000000000000 : ℝ) < t → t ≤ (54051600444471 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-18174836265096459405733843 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (54051600444471 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_673
  have hV : (5945398544644444458866490186208833 / 1000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (106849838184611 / 128000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_672 (Vfield_monotoneOn (show (106849838184611 / 128000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (106849838184611 / 128000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_673 : (14956481661960375030059195551779107 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (54051600444471 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (54051600444471 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (45949870972203 / 50000000000000 : ℝ) ≤ Real.sqrt (54051600444471 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (54051600444471 / 64000000000000 : ℝ) ≤ (91899741944407 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (91899741944407 / 100000000000000 : ℝ) = (100000000000000 / 91899741944407 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (45949870972203 / 50000000000000 : ℝ) = (1250000000000 / 15316623657401 : ℝ) := by norm_num
  have hL1 : (61223873742397 / 100000000000000 : ℝ) ≤ Real.log (1 + (54051600444471 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((54051600444471 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-4057642712661 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (91899741944407 / 235814441682203 : ℝ) ≤ (371606160447363 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (91899741944407 / 100000000000000 : ℝ) ≤ (371606160447363 / 500000000000000 : ℝ) := by
    have hw : (135814441682203 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (91899741944407 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (91899741944407 / 100000000000000 : ℝ) / (1 + (135814441682203 / 100000000000000 : ℝ)) = (91899741944407 / 235814441682203 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (82758400590017061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 91899741944407 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 91899741944407 : ℝ) = (91899741944407 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 15316623657401 : ℝ) ≤ (1017877649923 / 12500000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (82758400590017061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (91899741944407 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (45949870972203 / 50000000000000 : ℝ)) ≤ (1017877649923 / 12500000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_673 : ∀ t : ℝ, (54051600444471 / 64000000000000 : ℝ) < t → t ≤ (27652481574401 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-33532509924589059581636447 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (27652481574401 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_674
  have hV : (14956481661960375030059195551779107 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (54051600444471 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_673 (Vfield_monotoneOn (show (54051600444471 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (54051600444471 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_674 : (7570421564820144402830898356950507 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield (27652481574401 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (27652481574401 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (23239783362803 / 25000000000000 : ℝ) ≤ Real.sqrt (27652481574401 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (27652481574401 / 32000000000000 : ℝ) ≤ (92959133451213 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (92959133451213 / 100000000000000 : ℝ) = (100000000000000 / 92959133451213 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (23239783362803 / 25000000000000 : ℝ) = (1875000000000 / 23239783362803 : ℝ) := by norm_num
  have hL1 : (6227998471319 / 10000000000000 : ℝ) ≤ Real.log (1 + (27652481574401 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((27652481574401 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-6976608096833 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (92959133451213 / 236533514171431 : ℝ) ≤ (374462722302839 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (92959133451213 / 100000000000000 : ℝ) ≤ (374462722302839 / 500000000000000 : ℝ) := by
    have hw : (136533514171431 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (92959133451213 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (92959133451213 / 100000000000000 : ℝ) / (1 + (136533514171431 / 100000000000000 : ℝ)) = (92959133451213 / 236533514171431 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (82187088218921861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 92959133451213 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 92959133451213 : ℝ) = (92959133451213 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1875000000000 / 23239783362803 : ℝ) ≤ (80506235180617 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (82187088218921861923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (92959133451213 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (23239783362803 / 25000000000000 : ℝ)) ≤ (80506235180617 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_674 : ∀ t : ℝ, (27652481574401 / 32000000000000 : ℝ) < t → t ≤ (56558325853133 / 64000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-15407952694866375915154457 / 50000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (56558325853133 / 64000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_675
  have hV : (7570421564820144402830898356950507 / 1250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (27652481574401 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_674 (Vfield_monotoneOn (show (27652481574401 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (27652481574401 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_675 : (30646233222969942599804704150055619 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (56558325853133 / 64000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (56558325853133 / 64000000000000 : ℝ) := by norm_num
  have hs1 : (94006587080651 / 100000000000000 : ℝ) ≤ Real.sqrt (56558325853133 / 64000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (56558325853133 / 64000000000000 : ℝ) ≤ (23501646770163 / 25000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (23501646770163 / 25000000000000 : ℝ) = (25000000000000 / 23501646770163 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (94006587080651 / 100000000000000 : ℝ) = (7500000000000 / 94006587080651 : ℝ) := by norm_num
  have hL1 : (3166252922207 / 5000000000000 : ℝ) ≤ Real.log (1 + (56558325853133 / 64000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((56558325853133 / 64000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-2931643064717 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (4947715109508 / 12486779966093 : ℝ) ≤ (47157197086421 / 125000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (23501646770163 / 25000000000000 : ℝ) ≤ (47157197086421 / 62500000000000 : ℝ) := by
    have hw : (137248819355767 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (23501646770163 / 25000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (23501646770163 / 25000000000000 : ℝ) / (1 + (137248819355767 / 100000000000000 : ℝ)) = (4947715109508 / 12486779966093 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (81628117341216061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (25000000000000 / 23501646770163 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (25000000000000 / 23501646770163 : ℝ) = (23501646770163 / 25000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 94006587080651 : ℝ) ≤ (79613013863201 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (81628117341216061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (23501646770163 / 25000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (94006587080651 / 100000000000000 : ℝ)) ≤ (79613013863201 / 1000000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_675 : ∀ t : ℝ, (56558325853133 / 64000000000000 : ℝ) < t → t ≤ (7226461069683 / 8000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-7047678759931079854828071 / 25000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (7226461069683 / 8000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_676
  have hV : (30646233222969942599804704150055619 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (56558325853133 / 64000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_675 (Vfield_monotoneOn (show (56558325853133 / 64000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (56558325853133 / 64000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_676 : (31006736003949333025352385505746097 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield (7226461069683 / 8000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (7226461069683 / 8000000000000 : ℝ) := by norm_num
  have hs1 : (95042497531913 / 100000000000000 : ℝ) ≤ Real.sqrt (7226461069683 / 8000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (7226461069683 / 8000000000000 : ℝ) ≤ (47521248765957 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (47521248765957 / 50000000000000 : ℝ) = (50000000000000 / 47521248765957 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (95042497531913 / 100000000000000 : ℝ) = (7500000000000 / 95042497531913 : ℝ) := by norm_num
  have hL1 : (16089830811989 / 25000000000000 : ℝ) ≤ Real.log (1 + (7226461069683 / 8000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((7226461069683 / 8000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-9548429762063 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (95042497531914 / 237960415834049 : ℝ) ≤ (379993042391333 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (47521248765957 / 50000000000000 : ℝ) ≤ (379993042391333 / 500000000000000 : ℝ) := by
    have hw : (137960415834049 / 100000000000000 : ℝ) ≤ Real.sqrt (1 + (47521248765957 / 50000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (47521248765957 / 50000000000000 : ℝ) / (1 + (137960415834049 / 100000000000000 : ℝ)) = (95042497531914 / 237960415834049 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (81081024201223061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (50000000000000 / 47521248765957 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (50000000000000 / 47521248765957 : ℝ) = (47521248765957 / 50000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (7500000000000 / 95042497531913 : ℝ) ≤ (2460902463453 / 31250000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (81081024201223061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (47521248765957 / 50000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (95042497531913 / 100000000000000 : ℝ)) ≤ (2460902463453 / 31250000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_676 : ∀ t : ℝ, (7226461069683 / 8000000000000 : ℝ) < t → t ≤ (30159206983063 / 32000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2898184772562841876951017 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (30159206983063 / 32000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_677
  have hV : (31006736003949333025352385505746097 / 5000000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (7226461069683 / 8000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_676 (Vfield_monotoneOn (show (7226461069683 / 8000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (7226461069683 / 8000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_677 : (1585805154934694915414597517523541 / 250000000000000000000000000000000 : ℝ) ≤ Vfield (30159206983063 / 32000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (30159206983063 / 32000000000000 : ℝ) := by norm_num
  have hs1 : (4854058142989 / 5000000000000 : ℝ) ≤ Real.sqrt (30159206983063 / 32000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (30159206983063 / 32000000000000 : ℝ) ≤ (97081162859781 / 100000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (97081162859781 / 100000000000000 : ℝ) = (100000000000000 / 97081162859781 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (4854058142989 / 5000000000000 : ℝ) = (375000000000 / 4854058142989 : ℝ) := by norm_num
  have hL1 : (33198152275257 / 50000000000000 : ℝ) ≤ Real.log (1 + (30159206983063 / 32000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((30159206983063 / 32000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1065901332639 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (97081162859781 / 239372709603448 : ℝ) ≤ (385294457851603 / 1000000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (97081162859781 / 100000000000000 : ℝ) ≤ (385294457851603 / 500000000000000 : ℝ) := by
    have hw : (17421588700431 / 12500000000000 : ℝ) ≤ Real.sqrt (1 + (97081162859781 / 100000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (97081162859781 / 100000000000000 : ℝ) / (1 + (17421588700431 / 12500000000000 : ℝ)) = (97081162859781 / 239372709603448 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (80020741109169061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (100000000000000 / 97081162859781 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (100000000000000 / 97081162859781 : ℝ) = (97081162859781 / 100000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (375000000000 / 4854058142989 : ℝ) ≤ (38550899924529 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (80020741109169061923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (97081162859781 / 100000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (4854058142989 / 5000000000000 : ℝ)) ≤ (38550899924529 / 500000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_677 : ∀ t : ℝ, (30159206983063 / 32000000000000 : ℝ) < t → t ≤ (15706284843697 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-2308581850592452460843851 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (15706284843697 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_678
  have hV : (1585805154934694915414597517523541 / 250000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (30159206983063 / 32000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_677 (Vfield_monotoneOn (show (30159206983063 / 32000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (30159206983063 / 32000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_678 : (16205357906868573186695759252382283 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (15706284843697 / 16000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (15706284843697 / 16000000000000 : ℝ) := by norm_num
  have hs1 : (49538944345107 / 50000000000000 : ℝ) ≤ Real.sqrt (15706284843697 / 16000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (15706284843697 / 16000000000000 : ℝ) ≤ (19815577738043 / 20000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (19815577738043 / 20000000000000 : ℝ) = (20000000000000 / 19815577738043 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (49538944345107 / 50000000000000 : ℝ) = (1250000000000 / 16512981448369 : ℝ) := by norm_num
  have hL1 : (4274538744033 / 6250000000000 : ℝ) ≤ Real.log (1 + (15706284843697 / 16000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((15706284843697 / 16000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (-1281394607069 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA5 : Real.arctan (99077888690215 / 240770835144608 : ℝ) ≤ (97595785535009 / 250000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : Real.arctan (19815577738043 / 20000000000000 : ℝ) ≤ (97595785535009 / 125000000000000 : ℝ) := by
    have hw : (4399088598269 / 3125000000000 : ℝ) ≤ Real.sqrt (1 + (19815577738043 / 20000000000000 : ℝ) ^ 2) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
    have := arctan_le_half (by norm_num) (by norm_num) hw
    have e : (19815577738043 / 20000000000000 : ℝ) / (1 + (4399088598269 / 3125000000000 : ℝ)) = (99077888690215 / 240770835144608 : ℝ) := by norm_num
    rw [e] at this; linarith [hA5]
  have hA3 : (79003004251482461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (20000000000000 / 19815577738043 : ℝ) := by
    rw [arctan_eq_pi_div_two_sub (by norm_num)]
    have := Real.pi_gt_d20
    have e : (1 : ℝ) / (20000000000000 / 19815577738043 : ℝ) = (19815577738043 / 20000000000000 : ℝ) := by norm_num
    rw [e]; linarith [hA4]
  have hA6 : Real.arctan (1250000000000 / 16512981448369 : ℝ) ≤ (3022157082797 / 40000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (79003004251482461923 / 100000000000000000000 : ℝ) ≤ Real.arctan (1 / (19815577738043 / 20000000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (49538944345107 / 50000000000000 : ℝ)) ≤ (3022157082797 / 40000000000000 : ℝ) := by rw [e2]; exact hA6
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_678 : ∀ t : ℝ, (15706284843697 / 16000000000000 : ℝ) < t → t ≤ (4239911887007 / 4000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1220227708800417357648523 / 12500000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (4239911887007 / 4000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_679
  have hV : (16205357906868573186695759252382283 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (15706284843697 / 16000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_678 (Vfield_monotoneOn (show (15706284843697 / 16000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (15706284843697 / 16000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

lemma V_pt_679 : (16879483407812379011154472383747461 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield (4239911887007 / 4000000000000 : ℝ) := by
  have hp : (0 : ℝ) < (4239911887007 / 4000000000000 : ℝ) := by norm_num
  have hs1 : (102955231618007 / 100000000000000 : ℝ) ≤ Real.sqrt (4239911887007 / 4000000000000 : ℝ) := le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs2 : Real.sqrt (4239911887007 / 4000000000000 : ℝ) ≤ (12869403952251 / 12500000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (12869403952251 / 12500000000000 : ℝ) = (12500000000000 / 12869403952251 : ℝ) := by norm_num
  have e2 : (3 / 40 : ℝ) / (102955231618007 / 100000000000000 : ℝ) = (7500000000000 / 102955231618007 : ℝ) := by norm_num
  have hL1 : (3613476447087 / 5000000000000 : ℝ) ≤ Real.log (1 + (4239911887007 / 4000000000000 : ℝ)) := by
    refine le_trans ?_ (log_ge_of_pow_two (by norm_num) 0 11 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hL2 : Real.log ((4239911887007 / 4000000000000 : ℝ) + (3 / 40) ^ 2) ≤ (3177040480309 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA4 : (385419094969143 / 1000000000000000 : ℝ) ≤ Real.arctan (625000000000000000000000000 / 1540509157310254243122075681 : ℝ) := by
    refine le_trans ?_ (arctan_ge_partial (by norm_num) (by norm_num) 8)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA3 : (385419094969143 / 500000000000000 : ℝ) ≤ Real.arctan (12500000000000 / 12869403952251 : ℝ) := by
    have hw : Real.sqrt (1 + (12500000000000 / 12869403952251 : ℝ) ^ 2) ≤ (69703225030931 / 50000000000000 : ℝ) := sqrt_le_of_sq_le (by norm_num) (by norm_num)
    have := arctan_ge_half (by norm_num) hw
    have e : (12500000000000 / 12869403952251 : ℝ) / (1 + (69703225030931 / 50000000000000 : ℝ)) = (625000000000000000000000000 / 1540509157310254243122075681 : ℝ) := by norm_num
    rw [e] at this; linarith [hA4]
  have hA5 : Real.arctan (7500000000000 / 102955231618007 : ℝ) ≤ (36359372804887 / 500000000000000 : ℝ) := by
    refine le_trans (arctan_le_partial (by norm_num) (by norm_num) 8) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hA1' : (385419094969143 / 500000000000000 : ℝ) ≤ Real.arctan (1 / (12869403952251 / 12500000000000 : ℝ)) := by rw [e1]; exact hA3
  have hA2' : Real.arctan ((3 / 40) / (102955231618007 / 100000000000000 : ℝ)) ≤ (36359372804887 / 500000000000000 : ℝ) := by rw [e2]; exact hA5
  have := Vfield_ge_of_bounds_pos hp (by norm_num) hs1 hs2 hL1 hL2 hA1' hA2' (by norm_num)
  linarith

lemma I_679 : ∀ t : ℝ, (4239911887007 / 4000000000000 : ℝ) < t → t ≤ (18213010252359 / 16000000000000 : ℝ) → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t h1 h2
  have hU : Uρ t ≤ (-1856915886424111917654243 / 100000000000000000000000000 : ℝ) := by
    refine le_trans (Uρ_monotoneOn (show t ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by linarith)) (show (18213010252359 / 16000000000000 : ℝ) ∈ Set.Ici (bρ 1) by rw [bρ_1]; exact Set.mem_Ici.mpr (by norm_num)) h2) U_pt_680
  have hV : (16879483407812379011154472383747461 / 2500000000000000000000000000000000 : ℝ) ≤ Vfield t := by
    have hq : (59205079 / 10 ^ 10 : ℝ) ≤ (4239911887007 / 4000000000000 : ℝ) := by norm_num
    refine le_trans V_pt_679 (Vfield_monotoneOn (show (4239911887007 / 4000000000000 : ℝ) ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ (4239911887007 / 4000000000000 : ℝ); norm_num)) (show t ∈ Set.Ici qp from Set.mem_Ici.mpr (by show (59205079 / 10 ^ 10 : ℝ) ≤ t; linarith)) h1.le)
  show _ ≤ -1329 / 200
  linarith

end Apery
