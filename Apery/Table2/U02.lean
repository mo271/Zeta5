import Apery.Table2.Data

set_option maxHeartbeats 4000000

namespace Apery

lemma U_pt_80 : Uρ (1412931037823 / 32000000000000 : ℝ) ≤ (-266815056315630100554462937 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1412931037823 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (752370397419 / 20000000000000 : ℝ)) / 2) ≤ (-81977958645303 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-81977958645303 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1412931037823 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (694433060827 / 20000000000000 : ℝ)) / 2) ≤ (-67034113556909 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-67034113556909 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1412931037823 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (561304070089 / 20000000000000 : ℝ)) / 2) ≤ (-176463131474199 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-176463131474199 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1412931037823 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (246380746451 / 25000000000000 : ℝ)) / 2) ≤ (-102904271017491 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-102904271017491 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1412931037823 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_81 : Uρ (71843627457 / 1600000000000 : ℝ) ≤ (-266210277587880610566474171 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((71843627457 / 1600000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3836836625013 / 100000000000000 : ℝ)) / 2) ≤ (-325942556866427 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-325942556866427 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((71843627457 / 1600000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1774130081431 / 50000000000000 : ℝ)) / 2) ≤ (-333039071457889 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-333039071457889 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((71843627457 / 1600000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (57757610271 / 2000000000000 : ℝ)) / 2) ≤ (-175149182382091 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-175149182382091 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((71843627457 / 1600000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1147779541003 / 100000000000000 : ℝ)) / 2) ≤ (-16183999609189 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-16183999609189 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (71843627457 / 1600000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_82 : Uρ (2897686609597 / 64000000000000 : ℝ) ≤ (-13296510485435766534295287 / 5000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2897686609597 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3874326516543 / 100000000000000 : ℝ)) / 2) ≤ (-324972303631899 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-324972303631899 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2897686609597 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (5603574111 / 156250000000 : ℝ)) / 2) ≤ (-33199040078153 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-33199040078153 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2897686609597 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2928429743857 / 100000000000000 : ℝ)) / 2) ≤ (-872530030569 / 250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-872530030569 / 250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2897686609597 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (61128292283 / 5000000000000 : ℝ)) / 2) ≤ (-12545104477497 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-12545104477497 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2897686609597 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_83 : Uρ (1460814060457 / 32000000000000 : ℝ) ≤ (-33207751205360081762624789 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1460814060457 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (244488428239 / 6250000000000 : ℝ)) / 2) ≤ (-64802278758417 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-64802278758417 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1460814060457 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3624301822577 / 100000000000000 : ℝ)) / 2) ≤ (-330952789408991 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-330952789408991 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1460814060457 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2968896508349 / 100000000000000 : ℝ)) / 2) ≤ (-347743331758181 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-347743331758181 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1460814060457 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (129411569329 / 10000000000000 : ℝ)) / 2) ≤ (-99617568022351 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-99617568022351 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1460814060457 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_84 : Uρ (2945569632231 / 64000000000000 : ℝ) ≤ (-53080820996656203829591491 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2945569632231 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1974650837587 / 50000000000000 : ℝ)) / 2) ≤ (-161529824369763 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-161529824369763 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2945569632231 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3662303738449 / 100000000000000 : ℝ)) / 2) ≤ (-32992600293669 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-32992600293669 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2945569632231 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1504642066929 / 50000000000000 : ℝ)) / 2) ≤ (-346491810562319 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-346491810562319 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2945569632231 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1362938889563 / 100000000000000 : ℝ)) / 2) ≤ (-395654290539763 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-395654290539763 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2945569632231 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_85 : Uρ (742377785887 / 16000000000000 : ℝ) ≤ (-26515526631480464005573781 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((742377785887 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3986787029243 / 100000000000000 : ℝ)) / 2) ≤ (-10066152967187 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-10066152967187 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((742377785887 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3700293563029 / 100000000000000 : ℝ)) / 2) ≤ (-328909814441963 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-328909814441963 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((742377785887 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (19059973529 / 625000000000 : ℝ)) / 2) ≤ (-345256958991889 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-345256958991889 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((742377785887 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (285885866329 / 20000000000000 : ℝ)) / 2) ≤ (-392974783637469 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-392974783637469 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (742377785887 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_86 : Uρ (598690530973 / 12800000000000 : ℝ) ≤ (-33114313667328848692670889 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((598690530973 / 12800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4024270955087 / 100000000000000 : ℝ)) / 2) ≤ (-20073935236939 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-20073935236939 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((598690530973 / 12800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (934567916237 / 25000000000000 : ℝ)) / 2) ≤ (-256175003253 / 78125000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-256175003253 / 78125000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((598690530973 / 12800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (30898343751 / 1000000000000 : ℝ)) / 2) ≤ (-6880766185247 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-6880766185247 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((598690530973 / 12800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (746949265357 / 50000000000000 : ℝ)) / 2) ≤ (-97603831766279 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-97603831766279 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (598690530973 / 12800000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_87 : Uρ (1508697083091 / 32000000000000 : ℝ) ≤ (-132340515161362792836399933 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1508697083091 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4061753492249 / 100000000000000 : ℝ)) / 2) ≤ (-320257691339413 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-320257691339413 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1508697083091 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1888119198947 / 50000000000000 : ℝ)) / 2) ≤ (-326908359201001 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-326908359201001 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1508697083091 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1565001390719 / 50000000000000 : ℝ)) / 2) ≤ (-342835414023699 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-342835414023699 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1508697083091 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1556597646917 / 100000000000000 : ℝ)) / 2) ≤ (-387962579404101 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-387962579404101 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1508697083091 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_88 : Uρ (3041335677499 / 64000000000000 : ℝ) ≤ (-66113540493832765277969343 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((3041335677499 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4099234678821 / 100000000000000 : ℝ)) / 2) ≤ (-319340918207149 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-319340918207149 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3041335677499 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (381419410137 / 10000000000000 : ℝ)) / 2) ≤ (-8148066830639 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-8148066830639 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((3041335677499 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1585051826163 / 50000000000000 : ℝ)) / 2) ≤ (-170823922581757 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-170823922581757 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((3041335677499 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1617732504813 / 100000000000000 : ℝ)) / 2) ≤ (-38560552506157 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-38560552506157 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (3041335677499 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_89 : Uρ (191579824301 / 4000000000000 : ℝ) ≤ (-264233342347488651003523429 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((191579824301 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4136714551517 / 100000000000000 : ℝ)) / 2) ≤ (-318432489375289 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-318432489375289 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((191579824301 / 4000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (19260695507 / 500000000000 : ℝ)) / 2) ≤ (-162473373105941 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-162473373105941 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((191579824301 / 4000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (321013951871 / 10000000000000 : ℝ)) / 2) ≤ (-340475192676623 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-340475192676623 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((191579824301 / 4000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1677474139379 / 100000000000000 : ℝ)) / 2) ≤ (-38333494098949 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-38333494098949 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (191579824301 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_90 : Uρ (3089218700133 / 64000000000000 : ℝ) ≤ (-2640180923447080926450697 / 1000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((3089218700133 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2087096572863 / 50000000000000 : ℝ)) / 2) ≤ (-317532254035531 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-317532254035531 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3089218700133 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4862592139 / 125000000000 : ℝ)) / 2) ≤ (-40497548022413 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-40497548022413 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((3089218700133 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (812528195707 / 25000000000000 : ℝ)) / 2) ≤ (-21207316476177 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-21207316476177 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((3089218700133 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (433991598987 / 25000000000000 : ℝ)) / 2) ≤ (-381143011245979 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-381143011245979 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (3089218700133 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_91 : Uρ (62263204229 / 1280000000000 : ℝ) ≤ (-263807999098039104179613067 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((62263204229 / 1280000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (210583524779 / 5000000000000 : ℝ)) / 2) ≤ (-316640065438709 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-316640065438709 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((62263204229 / 1280000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3927998231799 / 100000000000000 : ℝ)) / 2) ≤ (-323023398948127 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-323023398948127 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((62263204229 / 1280000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (6580051453 / 200000000000 : ℝ)) / 2) ≤ (-42271635142181 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-42271635142181 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((62263204229 / 1280000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1793331529823 / 100000000000000 : ℝ)) / 2) ≤ (-379023042161723 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-379023042161723 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (62263204229 / 1280000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_92 : Uρ (3137101722767 / 64000000000000 : ℝ) ≤ (-5272054068532595295287093 / 2000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((3137101722767 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1062286658501 / 25000000000000 : ℝ)) / 2) ≤ (-315755780750217 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-315755780750217 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3137101722767 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (991478238159 / 25000000000000 : ℝ)) / 2) ≤ (-16103780395389 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-16103780395389 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((3137101722767 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (665976103757 / 20000000000000 : ℝ)) / 2) ≤ (-42130360446423 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-42130360446423 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((3137101722767 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (231209301563 / 12500000000000 : ℝ)) / 2) ≤ (-188484623871499 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-188484623871499 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (3137101722767 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_93 : Uρ (790260808521 / 16000000000000 : ℝ) ≤ (-65850472555529090042660049 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((790260808521 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1071655398193 / 25000000000000 : ℝ)) / 2) ≤ (-157439630455869 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-157439630455869 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((790260808521 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4003818152111 / 100000000000000 : ℝ)) / 2) ≤ (-160568416898357 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-160568416898357 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((790260808521 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (673935844607 / 20000000000000 : ℝ)) / 2) ≤ (-83981530903809 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-83981530903809 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((790260808521 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (952542872671 / 50000000000000 : ℝ)) / 2) ≤ (-11718018288127 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-11718018288127 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (790260808521 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_94 : Uρ (3184984745401 / 64000000000000 : ℝ) ≤ (-263205280961222679700824321 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((3184984745401 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2162047701277 / 50000000000000 : ℝ)) / 2) ≤ (-9812824078409 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-9812824078409 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3184984745401 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4041714098113 / 100000000000000 : ℝ)) / 2) ≤ (-12808276179723 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-12808276179723 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((3184984745401 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3409423803423 / 100000000000000 : ℝ)) / 2) ≤ (-167411233770761 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-167411233770761 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((3184984745401 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (489911138011 / 25000000000000 : ℝ)) / 2) ≤ (-373040627110607 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-373040627110607 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (3184984745401 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_95 : Uρ (1604463128359 / 32000000000000 : ℝ) ≤ (-32876578474501924940497333 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1604463128359 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2180784046483 / 50000000000000 : ℝ)) / 2) ≤ (-313148977645753 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-313148977645753 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1604463128359 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4079601048511 / 100000000000000 : ℝ)) / 2) ≤ (-63857130563141 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-63857130563141 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1604463128359 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (137964645239 / 4000000000000 : ℝ)) / 2) ≤ (-333731594476419 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-333731594476419 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1604463128359 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (100671006899 / 5000000000000 : ℝ)) / 2) ≤ (-185578730171491 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-185578730171491 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1604463128359 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_96 : Uρ (646573553607 / 12800000000000 : ℝ) ≤ (-262823708832220094544305989 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((646573553607 / 12800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4399039692613 / 100000000000000 : ℝ)) / 2) ≤ (-156147476910957 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-156147476910957 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((646573553607 / 12800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (514684906453 / 12500000000000 : ℝ)) / 2) ≤ (-318372916334711 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-318372916334711 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((646573553607 / 12800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3488757989167 / 100000000000000 : ℝ)) / 2) ≤ (-166326597862169 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-166326597862169 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((646573553607 / 12800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (82658945961 / 4000000000000 : ℝ)) / 2) ≤ (-369323605749523 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-369323605749523 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (646573553607 / 12800000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_97 : Uρ (407101159919 / 8000000000000 : ℝ) ≤ (-26263832431500417346508399 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((407101159919 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2218255114567 / 50000000000000 : ℝ)) / 2) ≤ (-155724086909297 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-155724086909297 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((407101159919 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4155348946661 / 100000000000000 : ℝ)) / 2) ≤ (-158734268595577 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-158734268595577 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((407101159919 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (705670215821 / 20000000000000 : ℝ)) / 2) ≤ (-165793487068803 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-165793487068803 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((407101159919 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2118859325349 / 100000000000000 : ℝ)) / 2) ≤ (-183767976556059 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-183767976556059 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (407101159919 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_98 : Uρ (1652346150993 / 32000000000000 : ℝ) ≤ (-262277452174722377792904327 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1652346150993 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1127862054689 / 25000000000000 : ℝ)) / 2) ≤ (-309775860141029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-309775860141029 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1652346150993 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4231063726263 / 100000000000000 : ℝ)) / 2) ≤ (-157842120656479 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-157842120656479 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1652346150993 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (721479475067 / 20000000000000 : ℝ)) / 2) ≤ (-329489928112883 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-329489928112883 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1652346150993 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2221815533047 / 100000000000000 : ℝ)) / 2) ≤ (-72817669883941 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-72817669883941 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1652346150993 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_99 : Uρ (167628766231 / 3200000000000 : ℝ) ≤ (-261928750710786828180321017 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((167628766231 / 3200000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2293191132543 / 50000000000000 : ℝ)) / 2) ≤ (-3851638704723 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-3851638704723 / 1250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((167628766231 / 3200000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4306747134039 / 100000000000000 : ℝ)) / 2) ≤ (-156965793700149 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-156965793700149 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((167628766231 / 3200000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3686267155727 / 100000000000000 : ℝ)) / 2) ≤ (-65487657744829 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-65487657744829 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((167628766231 / 3200000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1161309489201 / 50000000000000 : ℝ)) / 2) ≤ (-360795355168377 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-360795355168377 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (167628766231 / 3200000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_100 : Uρ (1700229173627 / 32000000000000 : ℝ) ≤ (-261591162414477307818339749 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1700229173627 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4661312558299 / 100000000000000 : ℝ)) / 2) ≤ (-153256494076289 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-153256494076289 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1700229173627 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (87648015907 / 2000000000000 : ℝ)) / 2) ≤ (-78052365153971 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-78052365153971 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1700229173627 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3764971513423 / 100000000000000 : ℝ)) / 2) ≤ (-325430039070777 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-325430039070777 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1700229173627 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (302692315119 / 12500000000000 : ℝ)) / 2) ≤ (-89410253819097 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-89410253819097 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1700229173627 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_101 : Uρ (107760667809 / 2000000000000 : ℝ) ≤ (-261263787803947779955024661 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((107760667809 / 2000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4736239276523 / 100000000000000 : ℝ)) / 2) ≤ (-19057542750547 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-19057542750547 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((107760667809 / 2000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (139313319519 / 3125000000000 : ℝ)) / 2) ≤ (-310516804616301 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-310516804616301 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((107760667809 / 2000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1921760305297 / 50000000000000 : ℝ)) / 2) ≤ (-80865824731547 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-80865824731547 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((107760667809 / 2000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (629699031867 / 25000000000000 : ℝ)) / 2) ≤ (-70922390302541 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-70922390302541 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (107760667809 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_102 : Uρ (886026853789 / 16000000000000 : ℝ) ≤ (-130318341808415576749657447 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((886026853789 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4886082645859 / 100000000000000 : ℝ)) / 2) ≤ (-1886314254427 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-1886314254427 / 625000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((886026853789 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (2304598972529 / 50000000000000 : ℝ)) / 2) ≤ (-12288637922293 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-12288637922293 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((886026853789 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (800037918087 / 20000000000000 : ℝ)) / 2) ≤ (-319647436327803 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-319647436327803 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((886026853789 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2709038552579 / 100000000000000 : ℝ)) / 2) ≤ (-348885858858791 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-348885858858791 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (886026853789 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_103 : Uρ (454984182553 / 8000000000000 : ℝ) ≤ (-260042348653150003796860641 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((454984182553 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2517956795427 / 50000000000000 : ℝ)) / 2) ≤ (-149396917734957 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-149396917734957 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((454984182553 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (2380136262321 / 50000000000000 : ℝ)) / 2) ≤ (-304021591026991 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-304021591026991 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((454984182553 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (519542523667 / 12500000000000 : ℝ)) / 2) ≤ (-157988976677531 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-157988976677531 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((454984182553 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1447258335757 / 50000000000000 : ℝ)) / 2) ≤ (-343543892155319 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-343543892155319 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (454984182553 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_104 : Uρ (47892569387 / 800000000000 : ℝ) ≤ (-129468440703463830543582073 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((47892569387 / 800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1333885598623 / 25000000000000 : ℝ)) / 2) ≤ (-4578456606149 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-4578456606149 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((47892569387 / 800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (5062165044447 / 100000000000000 : ℝ)) / 2) ≤ (-297926127575307 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-297926127575307 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((47892569387 / 800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (139603234489 / 3125000000000 : ℝ)) / 2) ≤ (-309034505146589 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-309034505146589 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((47892569387 / 800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1627209523263 / 50000000000000 : ℝ)) / 2) ≤ (-333802189150943 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-333802189150943 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (47892569387 / 800000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_105 : Uρ (502867205187 / 8000000000000 : ℝ) ≤ (-257923836930178654863566571 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((502867205187 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (5635132947063 / 100000000000000 : ℝ)) / 2) ≤ (-143782035914781 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-143782035914781 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((502867205187 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (107275270411 / 2000000000000 : ℝ)) / 2) ≤ (-36522961477287 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-36522961477287 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((502867205187 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2388386545177 / 50000000000000 : ℝ)) / 2) ≤ (-302557416663123 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-302557416663123 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((502867205187 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (3603246263843 / 100000000000000 : ℝ)) / 2) ≤ (-32506863110719 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-32506863110719 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (502867205187 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_106 : Uρ (65851089563 / 1000000000000 : ℝ) ≤ (-64246736312849356598865957 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((65851089563 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1186938208291 / 20000000000000 : ℝ)) / 2) ≤ (-282389651506177 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-282389651506177 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((65851089563 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (2832557457949 / 50000000000000 : ℝ)) / 2) ≤ (-57351070851151 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-57351070851151 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((65851089563 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (5085021677293 / 100000000000000 : ℝ)) / 2) ≤ (-296486294425859 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-296486294425859 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((65851089563 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1971969046677 / 50000000000000 : ℝ)) / 2) ≤ (-317133860239081 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-317133860239081 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_107 : Uρ (2140864814337 / 32000000000000 : ℝ) ≤ (-63731587659252223590190073 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2140864814337 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6039879386191 / 100000000000000 : ℝ)) / 2) ≤ (-280634326961617 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-280634326961617 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2140864814337 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (5770888392279 / 100000000000000 : ℝ)) / 2) ≤ (-71229339977613 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-71229339977613 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2140864814337 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1038603884961 / 20000000000000 : ℝ)) / 2) ≤ (-14722060556063 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-14722060556063 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2140864814337 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2031015056759 / 50000000000000 : ℝ)) / 2) ≤ (-31450832831503 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-31450832831503 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2140864814337 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (834877777861 / 100000000000000 : ℝ)) / 2) ≤ (-386237226980647 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-386237226980647 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2140864814337 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_108 : Uρ (1087247381329 / 16000000000000 : ℝ) ≤ (-253903311022885761071796077 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1087247381329 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6145064488403 / 100000000000000 : ℝ)) / 2) ≤ (-27890930966787 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-27890930966787 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1087247381329 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (2938318736397 / 50000000000000 : ℝ)) / 2) ≤ (-4423636655019 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-4423636655019 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1087247381329 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2650450214537 / 50000000000000 : ℝ)) / 2) ≤ (-292438201690787 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-292438201690787 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1087247381329 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1044857015539 / 25000000000000 : ℝ)) / 2) ≤ (-15597891306477 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-15597891306477 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1087247381329 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1190013080861 / 100000000000000 : ℝ)) / 2) ≤ (-375847718392123 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-375847718392123 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1087247381329 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_109 : Uρ (2208124710979 / 32000000000000 : ℝ) ≤ (-12652928877912746076026473 / 5000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2208124710979 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1562561627949 / 25000000000000 : ℝ)) / 2) ≤ (-138606784980467 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-138606784980467 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2208124710979 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1196472690233 / 20000000000000 : ℝ)) / 2) ≤ (-140670157161847 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-140670157161847 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2208124710979 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2704335837881 / 50000000000000 : ℝ)) / 2) ≤ (-145237764139943 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-145237764139943 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2208124710979 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2148094419191 / 50000000000000 : ℝ)) / 2) ≤ (-309477794853613 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-309477794853613 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2208124710979 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (734392722929 / 50000000000000 : ℝ)) / 2) ≤ (-183969126627601 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-183969126627601 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2208124710979 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_110 : Uρ (4449879370279 / 64000000000000 : ℝ) ≤ (-63168689559923259817878423 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4449879370279 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (393927276069 / 6250000000000 : ℝ)) / 2) ≤ (-69094092904361 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-69094092904361 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4449879370279 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (603521815647 / 10000000000000 : ℝ)) / 2) ≤ (-280465810104021 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-280465810104021 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4449879370279 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1092503634073 / 20000000000000 : ℝ)) / 2) ≤ (-289508804228019 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-289508804228019 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4449879370279 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4354346315573 / 100000000000000 : ℝ)) / 2) ≤ (-154131450146071 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-154131450146071 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4449879370279 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (398137378881 / 25000000000000 : ℝ)) / 2) ≤ (-45563122839147 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-45563122839147 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4449879370279 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_111 : Uρ (22417546593 / 320000000000 : ℝ) ≤ (-50461965646579349755061517 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((22417546593 / 320000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6355425609233 / 100000000000000 : ℝ)) / 2) ≤ (-275546129740951 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-275546129740951 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((22417546593 / 320000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (243522701239 / 4000000000000 : ℝ)) / 2) ≤ (-139799465432823 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-139799465432823 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((22417546593 / 320000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1379084899447 / 25000000000000 : ℝ)) / 2) ≤ (-288551560831557 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-288551560831557 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((22417546593 / 320000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1103090756353 / 25000000000000 : ℝ)) / 2) ≤ (-76766026397617 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-76766026397617 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((22417546593 / 320000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1708982025651 / 100000000000000 : ℝ)) / 2) ≤ (-361321537015869 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-361321537015869 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (22417546593 / 320000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_112 : Uρ (4517139266921 / 64000000000000 : ℝ) ≤ (-15747539875453784772346429 / 6250000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4517139266921 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3204007052871 / 50000000000000 : ℝ)) / 2) ≤ (-137361364793469 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-137361364793469 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4517139266921 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6140911712311 / 100000000000000 : ℝ)) / 2) ≤ (-5574790881 / 2000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-5574790881 / 2000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4517139266921 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (696267085583 / 12500000000000 : ℝ)) / 2) ≤ (-143801804858489 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-143801804858489 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4517139266921 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1117561112179 / 25000000000000 : ℝ)) / 2) ≤ (-305880952842051 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-305880952842051 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4517139266921 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (181949100019 / 10000000000000 : ℝ)) / 2) ≤ (-358342872933053 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-358342872933053 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4517139266921 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_113 : Uρ (2275384607621 / 32000000000000 : ℝ) ≤ (-25162488153044614127613059 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2275384607621 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3230300961809 / 50000000000000 : ℝ)) / 2) ≤ (-136953029614439 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-136953029614439 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2275384607621 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3096875416701 / 50000000000000 : ℝ)) / 2) ≤ (-55577504108809 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-55577504108809 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2275384607621 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (175747191547 / 3125000000000 : ℝ)) / 2) ≤ (-286664768186477 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-286664768186477 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2275384607621 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1131998943399 / 25000000000000 : ℝ)) / 2) ≤ (-76178251164829 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-76178251164829 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2275384607621 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1925096820089 / 100000000000000 : ℝ)) / 2) ≤ (-2777626112941 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-2777626112941 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2275384607621 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_114 : Uρ (4584399163563 / 64000000000000 : ℝ) ≤ (-125650403642100033919032893 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4584399163563 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3256594539649 / 50000000000000 : ℝ)) / 2) ≤ (-273096009466647 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-273096009466647 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4584399163563 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6246585022659 / 100000000000000 : ℝ)) / 2) ≤ (-277042734587329 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-277042734587329 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4584399163563 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1419415151013 / 25000000000000 : ℝ)) / 2) ≤ (-285734858988067 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-285734858988067 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4584399163563 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4585621915433 / 100000000000000 : ℝ)) / 2) ≤ (-30355984291079 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-30355984291079 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4584399163563 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (2026566151113 / 100000000000000 : ℝ)) / 2) ≤ (-70575301633353 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-70575301633353 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4584399163563 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_115 : Uρ (1154507277971 / 16000000000000 : ℝ) ≤ (-62746761387075434710655623 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1154507277971 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1313155117739 / 20000000000000 : ℝ)) / 2) ≤ (-272292473738589 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-272292473738589 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1154507277971 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (251976576167 / 4000000000000 : ℝ)) / 2) ≤ (-276205063554071 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-276205063554071 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1154507277971 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (5731388754573 / 100000000000000 : ℝ)) / 2) ≤ (-284813710097293 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-284813710097293 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1154507277971 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4643127535193 / 100000000000000 : ℝ)) / 2) ≤ (-37802633444607 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-37802633444607 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1154507277971 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (2124491773137 / 100000000000000 : ℝ)) / 2) ≤ (-43793080336287 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-43793080336287 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1154507277971 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_116 : Uρ (930331812041 / 12800000000000 : ℝ) ≤ (-62670624852976355913084093 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((930331812041 / 12800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6618361467213 / 100000000000000 : ℝ)) / 2) ≤ (-271495348037181 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-271495348037181 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((930331812041 / 12800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3176119548951 / 50000000000000 : ℝ)) / 2) ≤ (-275374388000139 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-275374388000139 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((930331812041 / 12800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (5785095203059 / 100000000000000 : ℝ)) / 2) ≤ (-56780230902001 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-56780230902001 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((930331812041 / 12800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4700517056241 / 100000000000000 : ℝ)) / 2) ≤ (-301296295574869 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-301296295574869 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((930331812041 / 12800000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (221934282043 / 10000000000000 : ℝ)) / 2) ≤ (-347925151041781 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-347925151041781 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (930331812041 / 12800000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_117 : Uρ (2342644504263 / 32000000000000 : ℝ) ≤ (-125193136454299365082380403 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2342644504263 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6670946729771 / 100000000000000 : ℝ)) / 2) ≤ (-135352265413981 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-135352265413981 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2342644504263 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (256202368793 / 4000000000000 : ℝ)) / 2) ≤ (-27455059145463 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-27455059145463 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2342644504263 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1459695137093 / 25000000000000 : ℝ)) / 2) ≤ (-17687314377839 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-17687314377839 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2342644504263 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4757794679799 / 100000000000000 : ℝ)) / 2) ≤ (-150092579982677 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-150092579982677 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2342644504263 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1155748907227 / 50000000000000 : ℝ)) / 2) ≤ (-345605530732731 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-345605530732731 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2342644504263 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_118 : Uρ (9404207965373 / 128000000000000 : ℝ) ≤ (-2502410420614166946394679 / 1000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((9404207965373 / 128000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (33486195673 / 500000000000 : ℝ)) / 2) ≤ (-270311456835407 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-270311456835407 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((9404207965373 / 128000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3215733800781 / 50000000000000 : ℝ)) / 2) ≤ (-13707061860413 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-13707061860413 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((9404207965373 / 128000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (5865615488423 / 100000000000000 : ℝ)) / 2) ≤ (-8829627502353 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-8829627502353 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((9404207965373 / 128000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4786392785687 / 100000000000000 : ℝ)) / 2) ≤ (-29963459526641 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-29963459526641 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((9404207965373 / 128000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (2356663492363 / 100000000000000 : ℝ)) / 2) ≤ (-344479876633689 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-344479876633689 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (9404207965373 / 128000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_119 : Uρ (4718918956847 / 64000000000000 : ℝ) ≤ (-250097621884485404232769751 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4718918956847 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3361765695411 / 50000000000000 : ℝ)) / 2) ≤ (-26991992297169 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-26991992297169 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4718918956847 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6457874882127 / 100000000000000 : ℝ)) / 2) ≤ (-273733560345799 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-273733560345799 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4718918956847 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1473111341829 / 25000000000000 : ℝ)) / 2) ≤ (-70525294789741 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-70525294789741 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4718918956847 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (300935274949 / 6250000000000 : ℝ)) / 2) ≤ (-299087308831827 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-299087308831827 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4718918956847 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (600316794963 / 25000000000000 : ℝ)) / 2) ≤ (-21460966314897 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-21460966314897 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4718918956847 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

end Apery
