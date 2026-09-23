import Apery.Table2.Data

set_option maxHeartbeats 4000000

namespace Apery

lemma U_pt_120 : Uρ (1894293572403 / 25600000000000 : ℝ) ≤ (-249955937413059993818847327 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1894293572403 / 25600000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (421863968761 / 6250000000000 : ℝ)) / 2) ≤ (-26952991720637 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-26952991720637 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1894293572403 / 25600000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6484281074973 / 100000000000000 : ℝ)) / 2) ≤ (-273327547108053 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-273327547108053 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1894293572403 / 25600000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (5919270253871 / 100000000000000 : ℝ)) / 2) ≤ (-5633126165971 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-5633126165971 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1894293572403 / 25600000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1210877497281 / 25000000000000 : ℝ)) / 2) ≤ (-9329476840451 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-9329476840451 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1894293572403 / 25600000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (244533962971 / 10000000000000 : ℝ)) / 2) ≤ (-342291252827153 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-342291252827153 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1894293572403 / 25600000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_121 : Uρ (297034306573 / 4000000000000 : ℝ) ≤ (-49963183878705260116541519 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((297034306573 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (677611546437 / 10000000000000 : ℝ)) / 2) ≤ (-134570713824773 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-134570713824773 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((297034306573 / 4000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6510686193337 / 100000000000000 : ℝ)) / 2) ≤ (-136461591952617 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-136461591952617 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((297034306573 / 4000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (5946090215657 / 100000000000000 : ℝ)) / 2) ≤ (-2249707590113 / 800000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-2249707590113 / 800000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((297034306573 / 4000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (9515683619 / 195312500000 : ℝ)) / 2) ≤ (-149001202263891 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-149001202263891 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((297034306573 / 4000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1244454531413 / 50000000000000 : ℝ)) / 2) ≤ (-170613151318133 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-170613151318133 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (297034306573 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_122 : Uρ (9538727758657 / 128000000000000 : ℝ) ≤ (-249677503671267147367474199 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((9538727758657 / 128000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (212575227659 / 3125000000000 : ℝ)) / 2) ≤ (-26875444254963 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-26875444254963 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((9538727758657 / 128000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6537090250237 / 100000000000000 : ℝ)) / 2) ≤ (-272520457314239 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-272520457314239 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((9538727758657 / 128000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1493226329753 / 25000000000000 : ℝ)) / 2) ≤ (-8774143190271 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-8774143190271 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((9538727758657 / 128000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1225131229241 / 25000000000000 : ℝ)) / 2) ≤ (-37183088202841 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-37183088202841 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((9538727758657 / 128000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1266000723163 / 50000000000000 : ℝ)) / 2) ≤ (-340179734015329 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-340179734015329 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (9538727758657 / 128000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_123 : Uρ (4786178853489 / 64000000000000 : ℝ) ≤ (-124770315330541651855706801 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4786178853489 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3414349481993 / 50000000000000 : ℝ)) / 2) ≤ (-134184475145619 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-134184475145619 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4786178853489 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1312698651697 / 20000000000000 : ℝ)) / 2) ≤ (-272119354075853 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-272119354075853 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4786178853489 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (149992890727 / 2500000000000 : ℝ)) / 2) ≤ (-280333690063039 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-280333690063039 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4786178853489 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1232248784223 / 25000000000000 : ℝ)) / 2) ≤ (-296930122864831 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-296930122864831 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4786178853489 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (514928146761 / 20000000000000 : ℝ)) / 2) ≤ (-169575367890131 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-169575367890131 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4786178853489 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_124 : Uρ (9605987655299 / 128000000000000 : ℝ) ≤ (-249405244886935742895020033 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((9605987655299 / 128000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3427495251349 / 50000000000000 : ℝ)) / 2) ≤ (-8374529356033 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-8374529356033 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((9605987655299 / 128000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1317979046137 / 20000000000000 : ℝ)) / 2) ≤ (-271719861092127 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-271719861092127 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((9605987655299 / 128000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (6026521209833 / 100000000000000 : ℝ)) / 2) ≤ (-139948377365557 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-139948377365557 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((9605987655299 / 128000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2478720548993 / 50000000000000 : ℝ)) / 2) ≤ (-29639861771267 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-29639861771267 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((9605987655299 / 128000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1308424536889 / 50000000000000 : ℝ)) / 2) ≤ (-338138555369233 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-338138555369233 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (9605987655299 / 128000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_125 : Uρ (481980880181 / 6400000000000 : ℝ) ≤ (-249271294580185520743868697 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((481980880181 / 6400000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1720320475707 / 25000000000000 : ℝ)) / 2) ≤ (-3345029981323 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-3345029981323 / 1250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((481980880181 / 6400000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (165407404481 / 2500000000000 : ℝ)) / 2) ≤ (-271321965423741 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-271321965423741 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((481980880181 / 6400000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (6053322124099 / 100000000000000 : ℝ)) / 2) ≤ (-27946175838507 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-27946175838507 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((481980880181 / 6400000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4985863215463 / 100000000000000 : ℝ)) / 2) ≤ (-295870152376723 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-295870152376723 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((481980880181 / 6400000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (2658646991327 / 100000000000000 : ℝ)) / 2) ≤ (-337142493045413 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-337142493045413 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (481980880181 / 6400000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_126 : Uρ (9673247551941 / 128000000000000 : ℝ) ≤ (-49827746265498395485769121 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((9673247551941 / 128000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6907573165961 / 100000000000000 : ℝ)) / 2) ≤ (-10688852656413 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-10688852656413 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((9673247551941 / 128000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1328539223271 / 20000000000000 : ℝ)) / 2) ≤ (-270925654287449 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-270925654287449 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((9673247551941 / 128000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3040059216793 / 50000000000000 : ℝ)) / 2) ≤ (-69757170890187 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-69757170890187 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((9673247551941 / 128000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (200570475791 / 4000000000000 : ℝ)) / 2) ≤ (-11813787591969 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-11813787591969 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((9673247551941 / 128000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (2700053547033 / 100000000000000 : ℝ)) / 2) ≤ (-168080948409047 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-168080948409047 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (9673247551941 / 128000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_127 : Uρ (4853438750131 / 64000000000000 : ℝ) ≤ (-62251877440255292728959381 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4853438750131 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3466932146827 / 50000000000000 : ℝ)) / 2) ≤ (-266841682015309 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-266841682015309 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4853438750131 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3334547527021 / 50000000000000 : ℝ)) / 2) ≤ (-270530915053557 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-270530915053557 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4853438750131 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (610691019891 / 10000000000000 : ℝ)) / 2) ≤ (-55719502606621 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-55719502606621 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4853438750131 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1008527506383 / 20000000000000 : ℝ)) / 2) ≤ (-147411096817241 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-147411096817241 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4853438750131 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1370543238281 / 50000000000000 : ℝ)) / 2) ≤ (-335196157976199 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-335196157976199 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4853438750131 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_128 : Uρ (1221767174613 / 16000000000000 : ℝ) ≤ (-248748923832938847213987451 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1221767174613 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6986446148837 / 100000000000000 : ℝ)) / 2) ≤ (-53217342518101 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-53217342518101 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1221767174613 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6721889978231 / 100000000000000 : ℝ)) / 2) ≤ (-269746102527299 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-269746102527299 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1221767174613 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (48128752611 / 781250000000 : ℝ)) / 2) ≤ (-867940053553 / 312500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-867940053553 / 312500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1221767174613 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (637415152251 / 12500000000000 : ℝ)) / 2) ≤ (-293785958608383 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-293785958608383 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1221767174613 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (352762062397 / 12500000000000 : ℝ)) / 2) ≤ (-41663376350129 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-41663376350129 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1221767174613 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_129 : Uρ (4920698646773 / 64000000000000 : ℝ) ≤ (-248495225116423016485412417 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4920698646773 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (7039027480381 / 100000000000000 : ℝ)) / 2) ≤ (-66334350997401 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-66334350997401 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4920698646773 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6774681044167 / 100000000000000 : ℝ)) / 2) ≤ (-67241857446587 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-67241857446587 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4920698646773 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3107016496977 / 50000000000000 : ℝ)) / 2) ≤ (-276891537539637 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-276891537539637 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4920698646773 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (644489657861 / 12500000000000 : ℝ)) / 2) ≤ (-36595146259113 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-36595146259113 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4920698646773 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (2901796781393 / 100000000000000 : ℝ)) / 2) ≤ (-33147090841709 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-33147090841709 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4920698646773 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_130 : Uρ (2477164297547 / 32000000000000 : ℝ) ≤ (-248246136045350992819081359 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2477164297547 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3545804149967 / 50000000000000 : ℝ)) / 2) ≤ (-10583746875953 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-10583746875953 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2477164297547 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (136549366827 / 2000000000000 : ℝ)) / 2) ≤ (-134097400538267 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-134097400538267 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2477164297547 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (6267568626103 / 100000000000000 : ℝ)) / 2) ≤ (-276049544559989 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-276049544559989 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2477164297547 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1042485704271 / 20000000000000 : ℝ)) / 2) ≤ (-58349512210221 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-58349512210221 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2477164297547 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (93134137563 / 3125000000000 : ℝ)) / 2) ≤ (-65936837953941 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-65936837953941 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2477164297547 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_131 : Uρ (997591708683 / 12800000000000 : ℝ) ≤ (-248001407922547394337805271 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((997591708683 / 12800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (7144188618801 / 100000000000000 : ℝ)) / 2) ≤ (-65963858468837 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-65963858468837 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((997591708683 / 12800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6880251956523 / 100000000000000 : ℝ)) / 2) ≤ (-66857030719059 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-66857030719059 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((997591708683 / 12800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3160543831647 / 50000000000000 : ℝ)) / 2) ≤ (-275214712021413 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-275214712021413 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((997591708683 / 12800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2634428860773 / 50000000000000 : ℝ)) / 2) ≤ (-7268621857383 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-7268621857383 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((997591708683 / 12800000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (38220951743 / 1250000000000 : ℝ)) / 2) ≤ (-327943600346687 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-327943600346687 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (997591708683 / 12800000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_132 : Uρ (627698561467 / 8000000000000 : ℝ) ≤ (-123880408336961373827358869 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((627698561467 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1439353689591 / 20000000000000 : ℝ)) / 2) ≤ (-131561304646169 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-131561304646169 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((627698561467 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1386606394757 / 20000000000000 : ℝ)) / 2) ≤ (-133333651913581 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-133333651913581 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((627698561467 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1274918104701 / 20000000000000 : ℝ)) / 2) ≤ (-137193458513149 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-137193458513149 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((627698561467 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1331301868021 / 25000000000000 : ℝ)) / 2) ≤ (-289752861801279 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-289752861801279 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((627698561467 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1567015178377 / 50000000000000 : ℝ)) / 2) ≤ (-326246231265461 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-326246231265461 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (627698561467 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_133 : Uρ (5055218440057 / 64000000000000 : ℝ) ≤ (-247524159389312553445619867 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((5055218440057 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (7249347798053 / 100000000000000 : ℝ)) / 2) ≤ (-13119755964297 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-13119755964297 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((5055218440057 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1397161694937 / 20000000000000 : ℝ)) / 2) ≤ (-132956127333953 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-132956127333953 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((5055218440057 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (6428077610673 / 100000000000000 : ℝ)) / 2) ≤ (-273566039865883 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-273566039865883 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((5055218440057 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (5381480268731 / 100000000000000 : ℝ)) / 2) ≤ (-144385642176553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-144385642176553 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((5055218440057 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (3209428533491 / 100000000000000 : ℝ)) / 2) ≤ (-324589469643719 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-324589469643719 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (5055218440057 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_134 : Uρ (2544424194189 / 32000000000000 : ℝ) ≤ (-61822812868387301520613851 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2544424194189 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (7301926679443 / 100000000000000 : ℝ)) / 2) ≤ (-130836443352127 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-130836443352127 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2544424194189 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3519290769161 / 50000000000000 : ℝ)) / 2) ≤ (-66290722042493 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-66290722042493 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2544424194189 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3240774657643 / 50000000000000 : ℝ)) / 2) ≤ (-136375981954611 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-136375981954611 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2544424194189 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (5437678500603 / 100000000000000 : ℝ)) / 2) ≤ (-287799911096659 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-287799911096659 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2544424194189 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (3283936521507 / 100000000000000 : ℝ)) / 2) ≤ (-322970957796951 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-322970957796951 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2544424194189 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_135 : Uρ (5122478336699 / 64000000000000 : ℝ) ≤ (-49412384856229445149178749 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((5122478336699 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (7354505102177 / 100000000000000 : ℝ)) / 2) ≤ (-260955836058091 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-260955836058091 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((5122478336699 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1418270248287 / 20000000000000 : ℝ)) / 2) ≤ (-52883823815253 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-52883823815253 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((5122478336699 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (6535006014941 / 100000000000000 : ℝ)) / 2) ≤ (-67986143874257 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-67986143874257 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((5122478336699 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1373451113989 / 25000000000000 : ℝ)) / 2) ≤ (-286838519139307 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-286838519139307 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((5122478336699 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (3357613583211 / 100000000000000 : ℝ)) / 2) ≤ (-160694279707199 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-160694279707199 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (5122478336699 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_136 : Uρ (257805414251 / 3200000000000 : ℝ) ≤ (-246836023137311811942994077 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((257805414251 / 3200000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (925885384503 / 12500000000000 : ℝ)) / 2) ≤ (-130121946736749 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-130121946736749 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((257805414251 / 3200000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (7144117658491 / 100000000000000 : ℝ)) / 2) ≤ (-131840432020947 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-131840432020947 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((257805414251 / 3200000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3294224037437 / 50000000000000 : ℝ)) / 2) ≤ (-2169150110721 / 800000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-2169150110721 / 800000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((257805414251 / 3200000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2774930163797 / 50000000000000 : ℝ)) / 2) ≤ (-285886893174009 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-285886893174009 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((257805414251 / 3200000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1715256628191 / 50000000000000 : ℝ)) / 2) ≤ (-39980041413279 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-39980041413279 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (257805414251 / 3200000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_137 : Uρ (2611684090831 / 32000000000000 : ℝ) ≤ (-246393940397127586446417283 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2611684090831 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3756118857377 / 50000000000000 : ℝ)) / 2) ≤ (-64708761199111 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-64708761199111 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2611684090831 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (45310255759 / 625000000000 : ℝ)) / 2) ≤ (-131110285996389 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-131110285996389 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2611684090831 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (6695289677737 / 100000000000000 : ℝ)) / 2) ≤ (-269561441406787 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-269561441406787 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2611684090831 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1415442535931 / 25000000000000 : ℝ)) / 2) ≤ (-56802422763957 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-56802422763957 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2611684090831 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (893542551163 / 25000000000000 : ℝ)) / 2) ≤ (-79209859953007 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-79209859953007 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2611684090831 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_138 : Uρ (165332127447 / 2000000000000 : ℝ) ≤ (-15372749241912602296996611 / 6250000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((165332127447 / 2000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (476086916777 / 6250000000000 : ℝ)) / 2) ≤ (-32180722535821 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-32180722535821 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((165332127447 / 2000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (7355151880551 / 100000000000000 : ℝ)) / 2) ≤ (-260781381394207 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-260781381394207 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((165332127447 / 2000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3401038408597 / 50000000000000 : ℝ)) / 2) ≤ (-268004164105339 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-268004164105339 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((165332127447 / 2000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (5773423766677 / 100000000000000 : ℝ)) / 2) ≤ (-141086994685769 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-141086994685769 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((165332127447 / 2000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (3715246078811 / 100000000000000 : ℝ)) / 2) ≤ (-313955783100931 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-313955783100931 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (165332127447 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_139 : Uρ (2678943987473 / 32000000000000 : ℝ) ≤ (-122772644821086169472119217 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2678943987473 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (7722542005891 / 100000000000000 : ℝ)) / 2) ≤ (-51215112526607 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-51215112526607 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2678943987473 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (7460651057837 / 100000000000000 : ℝ)) / 2) ≤ (-259362688777863 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-259362688777863 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2678943987473 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (863601502339 / 12500000000000 : ℝ)) / 2) ≤ (-53294227908783 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-53294227908783 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2678943987473 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (5884835778811 / 100000000000000 : ℝ)) / 2) ≤ (-140185518484107 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-140185518484107 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2678943987473 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (3854024328557 / 100000000000000 : ℝ)) / 2) ≤ (-4862168063719 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-4862168063719 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2678943987473 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_140 : Uρ (1356286967897 / 16000000000000 : ℝ) ≤ (-9805483288477005418422551 / 4000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1356286967897 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (7827691792263 / 100000000000000 : ℝ)) / 2) ≤ (-31840484543779 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-31840484543779 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1356286967897 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3783069473071 / 50000000000000 : ℝ)) / 2) ≤ (-32245489536541 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-32245489536541 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1356286967897 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (7015497652873 / 100000000000000 : ℝ)) / 2) ≤ (-52992322574621 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-52992322574621 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1356286967897 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (23984078593 / 400000000000 : ℝ)) / 2) ≤ (-6965046646989 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-6965046646989 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1356286967897 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (498843082617 / 12500000000000 : ℝ)) / 2) ≤ (-61699853338311 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-61699853338311 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1356286967897 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_141 : Uρ (694958458109 / 8000000000000 : ℝ) ≤ (-244349529556125521967906807 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((694958458109 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4018993477619 / 50000000000000 : ℝ)) / 2) ≤ (-126037069078077 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-126037069078077 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((694958458109 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1944270673309 / 25000000000000 : ℝ)) / 2) ≤ (-63805984970911 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-63805984970911 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((694958458109 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1807182249157 / 25000000000000 : ℝ)) / 2) ≤ (-10480408300609 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-10480408300609 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((694958458109 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (621775188903 / 10000000000000 : ℝ)) / 2) ≤ (-275159719815249 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-275159719815249 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((694958458109 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (851760289523 / 20000000000000 : ℝ)) / 2) ≤ (-37925304568171 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-37925304568171 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (694958458109 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_142 : Uρ (1423546864539 / 16000000000000 : ℝ) ≤ (-30449599884199640514046187 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1423546864539 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (8248276613283 / 100000000000000 : ℝ)) / 2) ≤ (-124746417929961 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-124746417929961 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1423546864539 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (7987986553651 / 100000000000000 : ℝ)) / 2) ≤ (-50511457919117 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-50511457919117 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1423546864539 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (148835742743 / 2000000000000 : ℝ)) / 2) ≤ (-51828914945149 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-51828914945149 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1423546864539 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (402419357137 / 6250000000000 : ℝ)) / 2) ≤ (-54367598714857 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-54367598714857 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1423546864539 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (4520740413957 / 100000000000000 : ℝ)) / 2) ≤ (-149306704408113 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-149306704408113 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1423546864539 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_143 : Uρ (72858840643 / 800000000000 : ℝ) ≤ (-242875238468221463778742269 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((72858840643 / 800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (528660073561 / 6250000000000 : ℝ)) / 2) ≤ (-246976521640323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-246976521640323 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((72858840643 / 800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (819885360547 / 10000000000000 : ℝ)) / 2) ≤ (-249960130551699 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-249960130551699 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((72858840643 / 800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1913671634277 / 25000000000000 : ℝ)) / 2) ≤ (-128179904183999 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-128179904183999 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((72858840643 / 800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1331794042823 / 20000000000000 : ℝ)) / 2) ≤ (-268628185059479 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-268628185059479 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((72858840643 / 800000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (4777567928279 / 100000000000000 : ℝ)) / 2) ≤ (-3676145772901 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-3676145772901 / 1250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (72858840643 / 800000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_144 : Uρ (762218354751 / 8000000000000 : ℝ) ≤ (-7547314892505408259154389 / 3125000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((762218354751 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1775823293819 / 20000000000000 : ℝ)) / 2) ≤ (-242126313110873 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-242126313110873 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((762218354751 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (344819523497 / 4000000000000 : ℝ)) / 2) ≤ (-61240096918011 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-61240096918011 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((762218354751 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (8080059297499 / 100000000000000 : ℝ)) / 2) ≤ (-6275381861731 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-6275381861731 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((762218354751 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (7097658717241 / 100000000000000 : ℝ)) / 2) ≤ (-52502938409383 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-52502938409383 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((762218354751 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (5278858782299 / 100000000000000 : ℝ)) / 2) ≤ (-142863237306173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-142863237306173 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (762218354751 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_145 : Uρ (24870259471 / 250000000000 : ℝ) ≤ (-240247173354219966584018127 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((24870259471 / 250000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4649827699869 / 50000000000000 : ℝ)) / 2) ≤ (-47500119138247 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-47500119138247 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((24870259471 / 250000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1808401044923 / 20000000000000 : ℝ)) / 2) ≤ (-9607976366267 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-9607976366267 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((24870259471 / 250000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (8504935021259 / 100000000000000 : ℝ)) / 2) ≤ (-7685776710479 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-7685776710479 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((24870259471 / 250000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (94178241429 / 1250000000000 : ℝ)) / 2) ≤ (-32095889903603 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-32095889903603 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((24870259471 / 250000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (5767232782939 / 100000000000000 : ℝ)) / 2) ≤ (-278111519237289 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-278111519237289 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_146 : Uρ (1614118950931 / 16000000000000 : ℝ) ≤ (-47594328496008753257235463 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1614118950931 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (73748802039 / 781250000000 : ℝ)) / 2) ≤ (-236004907417461 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-236004907417461 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1614118950931 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4591251280613 / 50000000000000 : ℝ)) / 2) ≤ (-238661453576939 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-238661453576939 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1614118950931 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2161619373309 / 25000000000000 : ℝ)) / 2) ≤ (-122155335635173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-122155335635173 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1614118950931 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (7679405859197 / 100000000000000 : ℝ)) / 2) ≤ (-3186559756911 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-3186559756911 / 1250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1614118950931 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (5927724944467 / 100000000000000 : ℝ)) / 2) ≤ (-275714822048579 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-275714822048579 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((1614118950931 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (1186679769539 / 100000000000000 : ℝ)) / 2) ≤ (-21629871195221 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-21629871195221 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1614118950931 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_147 : Uρ (818270647859 / 8000000000000 : ℝ) ≤ (-23680709076845664046206459 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((818270647859 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (9580036412143 / 100000000000000 : ℝ)) / 2) ≤ (-234531268589663 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-234531268589663 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((818270647859 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1165373641381 / 12500000000000 : ℝ)) / 2) ≤ (-47429370185057 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-47429370185057 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((818270647859 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (4393987500323 / 50000000000000 : ℝ)) / 2) ≤ (-242703019142863 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-242703019142863 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((818270647859 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1564873969761 / 20000000000000 : ℝ)) / 2) ≤ (-126558459037781 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-126558459037781 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((818270647859 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (6087212030779 / 100000000000000 : ℝ)) / 2) ≤ (-273381959033569 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-273381959033569 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((818270647859 / 8000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (422470117037 / 25000000000000 : ℝ)) / 2) ≤ (-168163330892357 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-168163330892357 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (818270647859 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_148 : Uρ (331792728101 / 3200000000000 : ℝ) ≤ (-117916831989837785656836073 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((331792728101 / 3200000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (151878511227 / 1562500000000 : ℝ)) / 2) ≤ (-7283719947273 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-7283719947273 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((331792728101 / 3200000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1892693082717 / 20000000000000 : ℝ)) / 2) ≤ (-29456862615513 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-29456862615513 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((331792728101 / 3200000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (8929429681043 / 100000000000000 : ℝ)) / 2) ≤ (-241121042774491 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-241121042774491 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((331792728101 / 3200000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (796916124553 / 10000000000000 : ℝ)) / 2) ≤ (-62835556308053 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-62835556308053 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((331792728101 / 3200000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (780721379597 / 12500000000000 : ℝ)) / 2) ≤ (-16944328858047 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-16944328858047 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((331792728101 / 3200000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (208385732803 / 10000000000000 : ℝ)) / 2) ≤ (-328896144058937 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-328896144058937 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (331792728101 / 3200000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_149 : Uρ (3340349625797 / 32000000000000 : ℝ) ≤ (-117694164753853826139525513 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((3340349625797 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (611894896833 / 6250000000000 : ℝ)) / 2) ≤ (-232360758678261 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-232360758678261 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3340349625797 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (9533699839229 / 100000000000000 : ℝ)) / 2) ≤ (-29364651298343 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-29364651298343 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((3340349625797 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (360005663687 / 4000000000000 : ℝ)) / 2) ≤ (-48067885387727 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-48067885387727 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((3340349625797 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (8041495135397 / 100000000000000 : ℝ)) / 2) ≤ (-250466929764569 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-250466929764569 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((3340349625797 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1581181084547 / 25000000000000 : ℝ)) / 2) ≤ (-26999442017161 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-26999442017161 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((3340349625797 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (2258444905067 / 100000000000000 : ℝ)) / 2) ≤ (-65133710315439 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-65133710315439 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (3340349625797 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_150 : Uρ (420346496323 / 4000000000000 : ℝ) ≤ (-58740825131334859605955899 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((420346496323 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (9860411641769 / 100000000000000 : ℝ)) / 2) ≤ (-231647603243683 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-231647603243683 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((420346496323 / 4000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (2400982965063 / 25000000000000 : ℝ)) / 2) ≤ (-117092467200587 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-117092467200587 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((420346496323 / 4000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (283463860563 / 3125000000000 : ℝ)) / 2) ≤ (-3743186369867 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-3743186369867 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((420346496323 / 4000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (8113789289191 / 100000000000000 : ℝ)) / 2) ≤ (-62399867590593 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-62399867590593 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((420346496323 / 4000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (25013558221 / 390625000000 : ℝ)) / 2) ≤ (-134446695782867 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-134446695782867 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((420346496323 / 4000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (2422499737111 / 100000000000000 : ℝ)) / 2) ≤ (-32267449515601 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-32267449515601 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (420346496323 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_151 : Uρ (3385194315371 / 32000000000000 : ℝ) ≤ (-234555210700152713759761383 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((3385194315371 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1241313075377 / 12500000000000 : ℝ)) / 2) ≤ (-230939499390643 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-230939499390643 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3385194315371 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (9674161529023 / 100000000000000 : ℝ)) / 2) ≤ (-116728996941317 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-116728996941317 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((3385194315371 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (9141535749783 / 100000000000000 : ℝ)) / 2) ≤ (-11939722457633 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-11939722457633 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((3385194315371 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (8186044759689 / 100000000000000 : ℝ)) / 2) ≤ (-248739703828819 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-248739703828819 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((3385194315371 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1620504567621 / 25000000000000 : ℝ)) / 2) ≤ (-267805803548093 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-267805803548093 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((3385194315371 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (1289016691593 / 50000000000000 : ℝ)) / 2) ≤ (-319871817426693 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-319871817426693 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (3385194315371 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_152 : Uρ (1703808330079 / 16000000000000 : ℝ) ≤ (-58540398987529972449391193 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1703808330079 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (10000597240033 / 100000000000000 : ℝ)) / 2) ≤ (-230236376034107 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-230236376034107 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1703808330079 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (2436097224101 / 25000000000000 : ℝ)) / 2) ≤ (-116368155735139 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-116368155735139 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1703808330079 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (9212218451567 / 100000000000000 : ℝ)) / 2) ≤ (-14876931113417 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-14876931113417 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1703808330079 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1032282820283 / 12500000000000 : ℝ)) / 2) ≤ (-247887490960683 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-247887490960683 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1703808330079 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (6560373590997 / 100000000000000 : ℝ)) / 2) ≤ (-8335353115431 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-8335353115431 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((1703808330079 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (681626127121 / 25000000000000 : ℝ)) / 2) ≤ (-79307445328567 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-79307445328567 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1703808330079 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_153 : Uρ (686007800989 / 6400000000000 : ℝ) ≤ (-233780585210702930188931863 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((686007800989 / 6400000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (10070689559589 / 100000000000000 : ℝ)) / 2) ≤ (-45907632715899 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-45907632715899 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((686007800989 / 6400000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1962922802359 / 20000000000000 : ℝ)) / 2) ≤ (-23201981147737 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-23201981147737 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((686007800989 / 6400000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2320722965151 / 25000000000000 : ℝ)) / 2) ≤ (-118636591136167 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-118636591136167 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((686007800989 / 6400000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2082610919141 / 25000000000000 : ℝ)) / 2) ≤ (-247042696397713 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-247042696397713 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((686007800989 / 6400000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (3319271833153 / 50000000000000 : ℝ)) / 2) ≤ (-265669538575649 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-265669538575649 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((686007800989 / 6400000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (1434504888993 / 50000000000000 : ℝ)) / 2) ≤ (-314725150396131 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-314725150396131 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (686007800989 / 6400000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_154 : Uρ (863115337433 / 8000000000000 : ℝ) ≤ (-233410715640457115818501957 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((863115337433 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2535195392067 / 25000000000000 : ℝ)) / 2) ≤ (-228844793881269 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-228844793881269 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((863115337433 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (9884836923193 / 100000000000000 : ℝ)) / 2) ≤ (-57827104960797 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-57827104960797 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((863115337433 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (584597261721 / 6250000000000 : ℝ)) / 2) ≤ (-1892169706039 / 800000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-1892169706039 / 800000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((863115337433 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (8402589048083 / 100000000000000 : ℝ)) / 2) ≤ (-123102594239657 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-123102594239657 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((863115337433 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (3358267482159 / 50000000000000 : ℝ)) / 2) ≤ (-13231009644717 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-13231009644717 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((863115337433 / 8000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (187899854259 / 6250000000000 : ℝ)) / 2) ≤ (-78084961724129 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-78084961724129 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (863115337433 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_155 : Uρ (6927345044251 / 64000000000000 : ℝ) ≤ (-14576848980634138752668123 / 6250000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((6927345044251 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2543956864509 / 25000000000000 : ℝ)) / 2) ≤ (-114249952078343 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-114249952078343 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((6927345044251 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4959973783511 / 50000000000000 : ℝ)) / 2) ≤ (-115477308474909 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-115477308474909 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6927345044251 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (586805313081 / 6250000000000 : ℝ)) / 2) ≤ (-1475920977237 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-1475920977237 / 625000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((6927345044251 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (8438648616797 / 100000000000000 : ℝ)) / 2) ≤ (-245789126845763 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-245789126845763 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((6927345044251 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (6755465507363 / 100000000000000 : ℝ)) / 2) ≤ (-264100077225047 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-264100077225047 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((6927345044251 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (614677612769 / 20000000000000 : ℝ)) / 2) ≤ (-155593664627967 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-155593664627967 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (6927345044251 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_156 : Uρ (3474883694519 / 32000000000000 : ℝ) ≤ (-46610163203430804374506211 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((3474883694519 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1276359159059 / 12500000000000 : ℝ)) / 2) ≤ (-228156200202989 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-228156200202989 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3474883694519 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (9955057677239 / 100000000000000 : ℝ)) / 2) ≤ (-230602064086689 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-230602064086689 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((3474883694519 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (9424211636659 / 100000000000000 : ℝ)) / 2) ≤ (-235774903540719 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-235774903540719 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((3474883694519 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4237349794829 / 50000000000000 : ℝ)) / 2) ≤ (-245374839107911 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-245374839107911 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((3474883694519 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (3397176820751 / 50000000000000 : ℝ)) / 2) ≤ (-52716589734539 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-52716589734539 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((3474883694519 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (3139340111123 / 100000000000000 : ℝ)) / 2) ≤ (-310059474177489 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-310059474177489 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (3474883694519 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_157 : Uρ (278887589353 / 2560000000000 : ℝ) ≤ (-232874299206989585613720537 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((278887589353 / 2560000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2561479753087 / 25000000000000 : ℝ)) / 2) ≤ (-1779794327281 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-1779794327281 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((278887589353 / 2560000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (624385453717 / 6250000000000 : ℝ)) / 2) ≤ (-230250752433153 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-230250752433153 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((278887589353 / 2560000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (945953609421 / 10000000000000 : ℝ)) / 2) ≤ (-23540384421047 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-23540384421047 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((278887589353 / 2560000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (85107420759 / 1000000000000 : ℝ)) / 2) ≤ (-122481154894459 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-122481154894459 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((278887589353 / 2560000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (683320009079 / 10000000000000 : ℝ)) / 2) ≤ (-131534384974563 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-131534384974563 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((278887589353 / 2560000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (640863585047 / 20000000000000 : ℝ)) / 2) ≤ (-30895489793009 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-30895489793009 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (278887589353 / 2560000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_158 : Uρ (1748653019653 / 16000000000000 : ℝ) ≤ (-116349964932861243308523341 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1748653019653 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (10280964678427 / 100000000000000 : ℝ)) / 2) ≤ (-113736158589359 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-113736158589359 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1748653019653 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (5012638159633 / 50000000000000 : ℝ)) / 2) ≤ (-229900673261811 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-229900673261811 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1748653019653 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (4747429203083 / 50000000000000 : ℝ)) / 2) ≤ (-117517083947371 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-117517083947371 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1748653019653 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1068347022861 / 12500000000000 : ℝ)) / 2) ≤ (-244551523618687 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-244551523618687 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1748653019653 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (3436002781071 / 50000000000000 : ℝ)) / 2) ≤ (-52511500901671 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-52511500901671 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((1748653019653 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (408547451517 / 12500000000000 : ℝ)) / 2) ≤ (-307872342915601 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-307872342915601 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1748653019653 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_159 : Uρ (7017034423399 / 64000000000000 : ℝ) ≤ (-232527613388328458353890169 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((7017034423399 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (5158005135731 / 50000000000000 : ℝ)) / 2) ≤ (-56783030525129 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-56783030525129 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((7017034423399 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (10060384862093 / 100000000000000 : ℝ)) / 2) ≤ (-5738795448429 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-5738795448429 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((7017034423399 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (297818081137 / 3125000000000 : ℝ)) / 2) ≤ (-58666466059909 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-58666466059909 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((7017034423399 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4291401008081 / 50000000000000 : ℝ)) / 2) ≤ (-15258904095631 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-15258904095631 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((7017034423399 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (6910770745859 / 100000000000000 : ℝ)) / 2) ≤ (-262049116526053 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-262049116526053 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((7017034423399 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (1665789009931 / 50000000000000 : ℝ)) / 2) ≤ (-306810662075591 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-306810662075591 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (7017034423399 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

end Apery
