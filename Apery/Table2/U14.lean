import Apery.Table2.Data

set_option maxHeartbeats 4000000

namespace Apery

lemma U_pt_560 : Uρ (5107553253053 / 8000000000000 : ℝ) ≤ (-37648998407042027591661681 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6319893186851 / 10000000000000 : ℝ)) / 2) ≤ (-4588787378951 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-4588787378951 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (31479191599471 / 50000000000000 : ℝ)) / 2) ≤ (-46266949715203 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-46266949715203 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (31237975965437 / 50000000000000 : ℝ)) / 2) ≤ (-47029371726063 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-47029371726063 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (12334148306803 / 20000000000000 : ℝ)) / 2) ≤ (-48308407002861 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-48308407002861 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (60434892709873 / 100000000000000 : ℝ)) / 2) ≤ (-25143763904661 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-25143763904661 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (58641644712177 / 100000000000000 : ℝ)) / 2) ≤ (-53194548384371 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-53194548384371 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (56153961395273 / 100000000000000 : ℝ)) / 2) ≤ (-28649284270643 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-28649284270643 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (52832124332111 / 100000000000000 : ℝ)) / 2) ≤ (-12582680652421 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-12582680652421 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (48537369732007 / 100000000000000 : ℝ)) / 2) ≤ (-8801814121631 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-8801814121631 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (43124794742429 / 100000000000000 : ℝ)) / 2) ≤ (-80287203512971 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-80287203512971 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (18203142716161 / 50000000000000 : ℝ)) / 2) ≤ (-23315333783771 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-23315333783771 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (7001857847261 / 25000000000000 : ℝ)) / 2) ≤ (-110761870303283 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-110761870303283 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((5107553253053 / 8000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (64714736851 / 390625000000 : ℝ)) / 2) ≤ (-68684053594003 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-68684053594003 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (5107553253053 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_561 : Uρ (20499005617149 / 32000000000000 : ℝ) ≤ (-74870660352842710512773431 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (63413910493339 / 100000000000000 : ℝ)) / 2) ≤ (-45548291969841 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-45548291969841 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (15793342889477 / 25000000000000 : ℝ)) / 2) ≤ (-2870379541949 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-2870379541949 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (15672742355931 / 25000000000000 : ℝ)) / 2) ≤ (-23342933534631 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-23342933534631 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1237716738221 / 2000000000000 : ℝ)) / 2) ≤ (-47960425357423 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-47960425357423 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (6065018172811 / 10000000000000 : ℝ)) / 2) ≤ (-9986488678139 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-9986488678139 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (14714346156541 / 25000000000000 : ℝ)) / 2) ≤ (-13207156710461 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-13207156710461 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (56370692476693 / 100000000000000 : ℝ)) / 2) ≤ (-56916470672803 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-56916470672803 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (26525468201869 / 50000000000000 : ℝ)) / 2) ≤ (-15626834489719 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-15626834489719 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (48760422042481 / 100000000000000 : ℝ)) / 2) ≤ (-34986308779149 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-34986308779149 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (867128547467 / 2000000000000 : ℝ)) / 2) ≤ (-7979003816777 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-7979003816777 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (36655834950349 / 100000000000000 : ℝ)) / 2) ≤ (-18534571285529 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-18534571285529 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (884340279439 / 3125000000000 : ℝ)) / 2) ≤ (-27499567217079 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-27499567217079 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((20499005617149 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (3400931211861 / 20000000000000 : ℝ)) / 2) ≤ (-136087383926981 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-136087383926981 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (20499005617149 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_562 : Uρ (10283899111043 / 16000000000000 : ℝ) ≤ (-74447121075095110967487169 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3976805569153 / 6250000000000 : ℝ)) / 2) ≤ (-45209859415939 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-45209859415939 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (31694179919541 / 50000000000000 : ℝ)) / 2) ≤ (-45586353713791 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-45586353713791 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (15726496659759 / 25000000000000 : ℝ)) / 2) ≤ (-9268707709871 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-9268707709871 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (48516352709 / 78125000000 : ℝ)) / 2) ≤ (-119034127717 / 250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-119034127717 / 250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (15216367134969 / 25000000000000 : ℝ)) / 2) ≤ (-387332946663 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-387332946663 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (59073118976757 / 100000000000000 : ℝ)) / 2) ≤ (-52464044105429 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-52464044105429 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (5658741017531 / 10000000000000 : ℝ)) / 2) ≤ (-56535839013931 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-56535839013931 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (53269717244511 / 100000000000000 : ℝ)) / 2) ≤ (-62102943937547 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-62102943937547 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (48983402139367 / 100000000000000 : ℝ)) / 2) ≤ (-69532738642437 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-69532738642437 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (10896972336707 / 25000000000000 : ℝ)) / 2) ≤ (-79295520902841 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-79295520902841 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (9226237325427 / 25000000000000 : ℝ)) / 2) ≤ (-46044183501329 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-46044183501329 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (28588991724501 / 100000000000000 : ℝ)) / 2) ≤ (-109242473745539 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-109242473745539 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((10283899111043 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (871700211177 / 5000000000000 : ℝ)) / 2) ≤ (-134838905147467 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-134838905147467 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (10283899111043 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_563 : Uρ (20636590827023 / 32000000000000 : ℝ) ≤ (-37013612939416703100287277 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (15960966926989 / 25000000000000 : ℝ)) / 2) ≤ (-44872568374923 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-44872568374923 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (31801674021627 / 50000000000000 : ℝ)) / 2) ≤ (-45247785000341 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-45247785000341 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (31560501789823 / 50000000000000 : ℝ)) / 2) ≤ (-9200475627659 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-9200475627659 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (15579006302981 / 25000000000000 : ℝ)) / 2) ≤ (-47268075837079 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-47268075837079 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (61080753168501 / 100000000000000 : ℝ)) / 2) ≤ (-49226040258031 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-49226040258031 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (11857769564937 / 20000000000000 : ℝ)) / 2) ≤ (-2605039519011 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-2605039519011 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (28402057322149 / 50000000000000 : ℝ)) / 2) ≤ (-56156662266217 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-56156662266217 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (10697693447531 / 20000000000000 : ℝ)) / 2) ≤ (-61700207262991 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-61700207262991 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (24603155502191 / 50000000000000 : ℝ)) / 2) ≤ (-69094857291569 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-69094857291569 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (43819183367207 / 100000000000000 : ℝ)) / 2) ≤ (-39401810876373 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-39401810876373 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (37153637239749 / 100000000000000 : ℝ)) / 2) ≤ (-228769515959 / 250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-228769515959 / 250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (28877780566027 / 100000000000000 : ℝ)) / 2) ≤ (-108494292197553 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-108494292197553 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((20636590827023 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (3571123682901 / 20000000000000 : ℝ)) / 2) ≤ (-33405133132177 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-33405133132177 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (20636590827023 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_564 : Uρ (517634585799 / 800000000000 : ℝ) ≤ (-18402708976492692956476219 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((517634585799 / 800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (64058846297979 / 100000000000000 : ℝ)) / 2) ≤ (-44536411172101 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-44536411172101 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((517634585799 / 800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (31909168085601 / 50000000000000 : ℝ)) / 2) ≤ (-22455179383777 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-22455179383777 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((517634585799 / 800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1979250632761 / 3125000000000 : ℝ)) / 2) ≤ (-9132475577993 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-9132475577993 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((517634585799 / 800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (195409744227 / 312500000000 : ℝ)) / 2) ≤ (-46923691340799 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-46923691340799 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((517634585799 / 800000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (15324008909247 / 25000000000000 : ℝ)) / 2) ≤ (-24437351921293 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-24437351921293 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((517634585799 / 800000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (59504571229799 / 100000000000000 : ℝ)) / 2) ≤ (-2069554239151 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-2069554239151 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((517634585799 / 800000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (14255201508623 / 25000000000000 : ℝ)) / 2) ≤ (-27889464631153 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-27889464631153 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((517634585799 / 800000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (26853593380049 / 50000000000000 : ℝ)) / 2) ≤ (-61299114176443 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-61299114176443 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((517634585799 / 800000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (49429149601219 / 100000000000000 : ℝ)) / 2) ≤ (-68658954768263 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-68658954768263 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((517634585799 / 800000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (4405031208009 / 10000000000000 : ℝ)) / 2) ≤ (-78314311285543 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-78314311285543 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((517634585799 / 800000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (3740190727023 / 10000000000000 : ℝ)) / 2) ≤ (-45465557787531 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-45465557787531 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((517634585799 / 800000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (3645661812223 / 12500000000000 : ℝ)) / 2) ≤ (-53876769661623 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-53876769661623 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((517634585799 / 800000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (365400681329 / 2000000000000 : ℝ)) / 2) ≤ (-827689728123 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-827689728123 / 625000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (517634585799 / 800000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_565 : Uρ (20774176036897 / 32000000000000 : ℝ) ≤ (-18299456144682472289748299 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (32136912438317 / 50000000000000 : ℝ)) / 2) ≤ (-44201380209921 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-44201380209921 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (64033324223693 / 100000000000000 : ℝ)) / 2) ≤ (-8914813466097 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-8914813466097 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (31775518323957 / 50000000000000 : ℝ)) / 2) ≤ (-45323529939071 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-45323529939071 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (31373105148967 / 50000000000000 : ℝ)) / 2) ≤ (-46580489415757 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-46580489415757 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (61511315968017 / 100000000000000 : ℝ)) / 2) ≤ (-24262299607889 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-24262299607889 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (59720289251079 / 100000000000000 : ℝ)) / 2) ≤ (-51378231319551 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-51378231319551 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (28618742247217 / 50000000000000 : ℝ)) / 2) ≤ (-11080525792781 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-11080525792781 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (53925876182601 / 100000000000000 : ℝ)) / 2) ≤ (-12179930218497 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-12179930218497 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (24825959437987 / 50000000000000 : ℝ)) / 2) ≤ (-68225012682097 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-68225012682097 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (22140639036987 / 50000000000000 : ℝ)) / 2) ≤ (-7782756058967 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-7782756058967 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (37649767660449 / 100000000000000 : ℝ)) / 2) ≤ (-18071647402441 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-18071647402441 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (29451570857803 / 100000000000000 : ℝ)) / 2) ≤ (-107020037615229 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-107020037615229 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((20774176036897 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (18677730342333 / 100000000000000 : ℝ)) / 2) ≤ (-131266663270363 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-131266663270363 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (20774176036897 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_566 : Uρ (10421484320917 / 16000000000000 : ℝ) ≤ (-909850949515378833833229 / 1250000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1007637553813 / 1562500000000 : ℝ)) / 2) ≤ (-43867467966941 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-43867467966941 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (12849662440297 / 20000000000000 : ℝ)) / 2) ≤ (-44238903081471 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-44238903081471 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (31883026390527 / 50000000000000 : ℝ)) / 2) ≤ (-8997165300009 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-8997165300009 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (31480650827979 / 50000000000000 : ℝ)) / 2) ≤ (-11559615490961 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-11559615490961 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (61726594183953 / 100000000000000 : ℝ)) / 2) ≤ (-12043929439603 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-12043929439603 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (59936001946657 / 100000000000000 : ℝ)) / 2) ≤ (-25509453462677 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-25509453462677 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (57454150170417 / 100000000000000 : ℝ)) / 2) ≤ (-11005550091957 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-11005550091957 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (10828907173977 / 20000000000000 : ℝ)) / 2) ≤ (-60501804596107 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-60501804596107 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (24937309878773 / 50000000000000 : ℝ)) / 2) ≤ (-67793012880413 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-67793012880413 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (22256041940913 / 50000000000000 : ℝ)) / 2) ≤ (-61874673009 / 80000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-61874673009 / 80000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (7579445289591 / 20000000000000 : ℝ)) / 2) ≤ (-8978911451243 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-8978911451243 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (29736645388623 / 100000000000000 : ℝ)) / 2) ≤ (-106293616549013 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-106293616549013 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((10421484320917 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (3815827599981 / 20000000000000 : ℝ)) / 2) ≤ (-16265988467253 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-16265988467253 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (10421484320917 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_567 : Uρ (20911761246771 / 32000000000000 : ℝ) ≤ (-1447629668160662627328529 / 2000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (64703782000287 / 100000000000000 : ℝ)) / 2) ≤ (-21767333498407 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-21767333498407 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (2578532004213 / 4000000000000 : ℝ)) / 2) ≤ (-21952429244551 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-21952429244551 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (31990534325229 / 50000000000000 : ℝ)) / 2) ≤ (-44649259865977 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-44649259865977 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (246782782167 / 390625000000 : ℝ)) / 2) ≤ (-45897600969891 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-45897600969891 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1935683447089 / 3125000000000 : ℝ)) / 2) ≤ (-373656647981 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-373656647981 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (60151709373829 / 100000000000000 : ℝ)) / 2) ≤ (-50660873421827 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-50660873421827 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (57670803206527 / 100000000000000 : ℝ)) / 2) ≤ (-13663570740957 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-13663570740957 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (3397697886297 / 6250000000000 : ℝ)) / 2) ≤ (-6010556143983 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-6010556143983 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (25048626579017 / 50000000000000 : ℝ)) / 2) ≤ (-67362937469163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-67362937469163 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (44742731982609 / 100000000000000 : ℝ)) / 2) ≤ (-76861625391787 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-76861625391787 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (38144291448867 / 100000000000000 : ℝ)) / 2) ≤ (-5576480826821 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-5576480826821 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (30020552327899 / 100000000000000 : ℝ)) / 2) ≤ (-26393528050301 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-26393528050301 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((20911761246771 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (19474645902423 / 100000000000000 : ℝ)) / 2) ≤ (-129012691036913 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-129012691036913 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (20911761246771 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_568 : Uρ (5245138462927 / 8000000000000 : ℝ) ≤ (-71977948430519159289483359 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (64918760545509 / 100000000000000 : ℝ)) / 2) ≤ (-21601484963647 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-21601484963647 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1293565758719 / 2000000000000 : ℝ)) / 2) ≤ (-21785963048601 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-21785963048601 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (64196084258777 / 100000000000000 : ℝ)) / 2) ≤ (-44313822407549 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-44313822407549 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (253565928169 / 400000000000 : ℝ)) / 2) ≤ (-45557898500543 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-45557898500543 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (62157144358451 / 100000000000000 : ℝ)) / 2) ≤ (-9496318065069 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-9496318065069 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (3772963224317 / 6250000000000 : ℝ)) / 2) ≤ (-1257603038399 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-1257603038399 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (14471860936171 / 25000000000000 : ℝ)) / 2) ≤ (-3392638488319 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-3392638488319 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (5458176746821 / 10000000000000 : ℝ)) / 2) ≤ (-59710908540881 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-59710908540881 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (50319819973121 / 100000000000000 : ℝ)) / 2) ≤ (-66934768807893 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-66934768807893 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (22486612401379 / 50000000000000 : ℝ)) / 2) ≤ (-38191192778121 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-38191192778121 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (19195485132913 / 50000000000000 : ℝ)) / 2) ≤ (-2770684987733 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-2770684987733 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (1212132979703 / 4000000000000 : ℝ)) / 2) ≤ (-104861366894247 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-104861366894247 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((5245138462927 / 8000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (993230322429 / 5000000000000 : ℝ)) / 2) ≤ (-127919741793801 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-127919741793801 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (5245138462927 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_569 : Uρ (10559069530791 / 16000000000000 : ℝ) ≤ (-8897461554974204833763227 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (65348717603291 / 100000000000000 : ℝ)) / 2) ≤ (-1063571459143 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-1063571459143 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3255413169023 / 5000000000000 : ℝ)) / 2) ≤ (-42909368460303 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-42909368460303 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3231305735129 / 5000000000000 : ℝ)) / 2) ≤ (-21823152441069 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-21823152441069 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (63821659374547 / 100000000000000 : ℝ)) / 2) ≤ (-44881937804663 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-44881937804663 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (15646921583317 / 25000000000000 : ℝ)) / 2) ≤ (-5849031796607 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-5849031796607 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (60798800605659 / 100000000000000 : ℝ)) / 2) ≤ (-49594426023189 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-49594426023189 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (29160343942117 / 50000000000000 : ℝ)) / 2) ≤ (-53542240500329 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-53542240500329 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (55018884356643 / 100000000000000 : ℝ)) / 2) ≤ (-58926321990943 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-58926321990943 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (50764757349977 / 100000000000000 : ℝ)) / 2) ≤ (-330420412061 / 500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-330420412061 / 500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (11358438513181 / 25000000000000 : ℝ)) / 2) ≤ (-18857806658777 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-18857806658777 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (9720799684063 / 25000000000000 : ℝ)) / 2) ≤ (-87549107335651 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-87549107335651 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (30865589126781 / 100000000000000 : ℝ)) / 2) ≤ (-25863887989607 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-25863887989607 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((10559069530791 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (20629139400417 / 100000000000000 : ℝ)) / 2) ≤ (-125796105512637 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-125796105512637 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (10559069530791 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_570 : Uρ (664241383483 / 1000000000000 : ℝ) ≤ (-351963251446177563633493 / 500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (32889337309117 / 50000000000000 : ℝ)) / 2) ≤ (-4188707574941 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-4188707574941 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (65538238540719 / 100000000000000 : ℝ)) / 2) ≤ (-10562792997133 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-10562792997133 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (8132018016621 / 12500000000000 : ℝ)) / 2) ≤ (-2686450900139 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-2686450900139 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (64251833714189 / 100000000000000 : ℝ)) / 2) ≤ (-22105259001949 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-22105259001949 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (12603644055293 / 20000000000000 : ℝ)) / 2) ≤ (-23053822057827 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-23053822057827 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (12246033886473 / 20000000000000 : ℝ)) / 2) ≤ (-48889748175121 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-48889748175121 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (58753883682647 / 100000000000000 : ℝ)) / 2) ≤ (-10561548322237 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-10561548322237 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (27727944623849 / 50000000000000 : ℝ)) / 2) ≤ (-29073971737473 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-29073971737473 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (51209438739203 / 100000000000000 : ℝ)) / 2) ≤ (-65240817458591 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-65240817458591 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (45893690045527 / 100000000000000 : ℝ)) / 2) ≤ (-74489654336463 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-74489654336463 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (39373968691021 / 100000000000000 : ℝ)) / 2) ≤ (-86450273526143 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-86450273526143 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (3142367625679 / 10000000000000 : ℝ)) / 2) ≤ (-25518755801273 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-25518755801273 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((664241383483 / 1000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (21374983414123 / 100000000000000 : ℝ)) / 2) ≤ (-123748836010523 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-123748836010523 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_571 : Uρ (4261528693017 / 6400000000000 : ℝ) ≤ (-34829757014656814886200803 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (65940923307781 / 100000000000000 : ℝ)) / 2) ≤ (-1041018069813 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-1041018069813 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (32850247007913 / 50000000000000 : ℝ)) / 2) ≤ (-42003916381 / 100000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-42003916381 / 100000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (65218419900949 / 100000000000000 : ℝ)) / 2) ≤ (-5341766105221 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-5341766105221 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (64414163659021 / 100000000000000 : ℝ)) / 2) ≤ (-1098957960069 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-1098957960069 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (63180684633333 / 100000000000000 : ℝ)) / 2) ≤ (-45850514199037 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-45850514199037 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (61392945735247 / 100000000000000 : ℝ)) / 2) ≤ (-48625120132437 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-48625120132437 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (29458671114039 / 50000000000000 : ℝ)) / 2) ≤ (-13132994341949 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-13132994341949 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (11124153794893 / 20000000000000 : ℝ)) / 2) ≤ (-57855807218639 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-57855807218639 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (51377178676549 / 100000000000000 : ℝ)) / 2) ≤ (-64924504045677 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-64924504045677 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (46067101105797 / 100000000000000 : ℝ)) / 2) ≤ (-74136791673131 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-74136791673131 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (7911759584863 / 20000000000000 : ℝ)) / 2) ≤ (-86039169961541 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-86039169961541 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (31633236109617 / 100000000000000 : ℝ)) / 2) ≤ (-6347525974037 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-6347525974037 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (4330395545933 / 20000000000000 : ℝ)) / 2) ≤ (-122994665858633 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-122994665858633 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((4261528693017 / 6400000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (821667395651 / 25000000000000 : ℝ)) / 2) ≤ (-169671151798769 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-169671151798769 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4261528693017 / 6400000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_572 : Uρ (10679781329357 / 16000000000000 : ℝ) ≤ (-69185235703237215865644859 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6610317199139 / 10000000000000 : ℝ)) / 2) ≤ (-41394975246783 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-41394975246783 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (32931374725771 / 50000000000000 : ℝ)) / 2) ≤ (-41757270649159 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-41757270649159 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (1634517388213 / 2500000000000 : ℝ)) / 2) ≤ (-42485662283587 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-42485662283587 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (16144123297341 / 25000000000000 : ℝ)) / 2) ≤ (-273167209807 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-273167209807 / 625000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1583578696961 / 2500000000000 : ℝ)) / 2) ≤ (-9118808924407 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-9118808924407 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (61555719245863 / 100000000000000 : ℝ)) / 2) ≤ (-48361192786341 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-48361192786341 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (59080794097037 / 100000000000000 : ℝ)) / 2) ≤ (-5225697712221 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-5225697712221 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (55785633265727 / 100000000000000 : ℝ)) / 2) ≤ (-57564535637229 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-57564535637229 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (12886220862877 / 25000000000000 : ℝ)) / 2) ≤ (-32304610783307 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-32304610783307 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (4624043112989 / 10000000000000 : ℝ)) / 2) ≤ (-14757050898929 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-14757050898929 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (39743429953159 / 100000000000000 : ℝ)) / 2) ≤ (-85629981693277 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-85629981693277 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (31842243522271 / 100000000000000 : ℝ)) / 2) ≤ (-101049201382259 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-101049201382259 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (21926673522159 / 100000000000000 : ℝ)) / 2) ≤ (-122250043319397 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-122250043319397 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((10679781329357 / 16000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (4653712752203 / 100000000000000 : ℝ)) / 2) ≤ (-6623357656193 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-6623357656193 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (10679781329357 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_573 : Uρ (21411481852343 / 32000000000000 : ℝ) ≤ (-1718870785725420258921963 / 2500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (13253084133821 / 20000000000000 : ℝ)) / 2) ≤ (-41149830143881 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-41149830143881 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (66025004848157 / 100000000000000 : ℝ)) / 2) ≤ (-1297225993489 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-1297225993489 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2621718840669 / 4000000000000 : ℝ)) / 2) ≤ (-42237811658213 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-42237811658213 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (64738822308337 / 100000000000000 : ℝ)) / 2) ≤ (-43455820314073 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-43455820314073 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (31752805010159 / 50000000000000 : ℝ)) / 2) ≤ (-45338231997209 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-45338231997209 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (241087851509 / 390625000000 : ℝ)) / 2) ≤ (-48097962424069 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-48097962424069 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (11848847868957 / 20000000000000 : ℝ)) / 2) ≤ (-25991368311013 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-25991368311013 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (13987620564483 / 25000000000000 : ℝ)) / 2) ≤ (-14318530886837 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-14318530886837 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (2068502136247 / 4000000000000 : ℝ)) / 2) ≤ (-64294963110167 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-64294963110167 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (23206840512843 / 50000000000000 : ℝ)) / 2) ≤ (-36717516135517 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-36717516135517 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (7985573502651 / 20000000000000 : ℝ)) / 2) ≤ (-8522268895539 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-8522268895539 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (16025354651193 / 50000000000000 : ℝ)) / 2) ≤ (-100541327441039 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-100541327441039 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (2219915611861 / 10000000000000 : ℝ)) / 2) ≤ (-15189331811107 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-15189331811107 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((21411481852343 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (5706534526699 / 100000000000000 : ℝ)) / 2) ≤ (-162451569336677 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-162451569336677 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (21411481852343 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_574 : Uρ (5365850261493 / 8000000000000 : ℝ) ≤ (-34173921584130904447420519 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (66427669340971 / 100000000000000 : ℝ)) / 2) ≤ (-4090528453727 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-4090528453727 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (66187260205959 / 100000000000000 : ℝ)) / 2) ≤ (-4126579682921 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-4126579682921 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (13141049273319 / 20000000000000 : ℝ)) / 2) ≤ (-8398114783791 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-8398114783791 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (32450575509513 / 50000000000000 : ℝ)) / 2) ≤ (-21602757736347 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-21602757736347 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (15917017766853 / 25000000000000 : ℝ)) / 2) ≤ (-22541536481577 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-22541536481577 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (966894655913 / 1562500000000 : ℝ)) / 2) ≤ (-47835425362377 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-47835425362377 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (5940767802597 / 10000000000000 : ℝ)) / 2) ≤ (-51709251650503 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-51709251650503 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (7014414510739 / 12500000000000 : ℝ)) / 2) ≤ (-3561535363299 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-3561535363299 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (12970047219539 / 25000000000000 : ℝ)) / 2) ≤ (-63981721836353 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-63981721836353 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (23293425843571 / 50000000000000 : ℝ)) / 2) ≤ (-9135764325457 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-9135764325457 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (40112113287137 / 100000000000000 : ℝ)) / 2) ≤ (-10602159038827 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-10602159038827 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (2016165246911 / 6250000000000 : ℝ)) / 2) ≤ (-25009185494197 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-25009185494197 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (11234753017969 / 50000000000000 : ℝ)) / 2) ≤ (-120788202494141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-120788202494141 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((5365850261493 / 8000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (3298661801337 / 50000000000000 : ℝ)) / 2) ≤ (-9988379581059 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-9988379581059 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (5365850261493 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_575 : Uρ (21515320239601 / 32000000000000 : ℝ) ≤ (-33978164130025198872990949 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (16647479501757 / 25000000000000 : ℝ)) / 2) ≤ (-5082666937747 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-5082666937747 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4146844720327 / 6250000000000 : ℝ)) / 2) ≤ (-10255240701119 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-10255240701119 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (65867521579153 / 100000000000000 : ℝ)) / 2) ≤ (-41743946041677 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-41743946041677 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (8132934915561 / 12500000000000 : ℝ)) / 2) ≤ (-214779179519 / 500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-214779179519 / 500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (31915265514041 / 50000000000000 : ℝ)) / 2) ≤ (-44828564184229 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-44828564184229 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (496352185951 / 800000000000 : ℝ)) / 2) ≤ (-11893394486809 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-11893394486809 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (29785555097321 / 50000000000000 : ℝ)) / 2) ≤ (-51436518026151 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-51436518026151 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (11256026976581 / 20000000000000 : ℝ)) / 2) ≤ (-5669585734391 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-5669585734391 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (13011947550159 / 25000000000000 : ℝ)) / 2) ≤ (-31834745487723 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-31834745487723 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (23379971997283 / 50000000000000 : ℝ)) / 2) ≤ (-2909539648917 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-2909539648917 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (4029616990551 / 10000000000000 : ℝ)) / 2) ≤ (-84413712642767 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-84413712642767 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (32466057672031 / 100000000000000 : ℝ)) / 2) ≤ (-9953539452871 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-9953539452871 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (22737799346227 / 100000000000000 : ℝ)) / 2) ≤ (-15008800777567 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-15008800777567 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((21515320239601 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (73849488571 / 1000000000000 : ℝ)) / 2) ≤ (-157493209313587 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-157493209313587 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (21515320239601 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_576 : Uρ (43082559672831 / 64000000000000 : ℝ) ≤ (-67765019167362973157608471 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (16667760584473 / 25000000000000 : ℝ)) / 2) ≤ (-40539583790363 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-40539583790363 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (66430643170509 / 100000000000000 : ℝ)) / 2) ≤ (-81797540451 / 200000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-81797540451 / 200000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (32974329567129 / 50000000000000 : ℝ)) / 2) ≤ (-832417197247 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-832417197247 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (32572321663103 / 50000000000000 : ℝ)) / 2) ≤ (-42831229621349 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-42831229621349 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (31955880301799 / 50000000000000 : ℝ)) / 2) ≤ (-5587694075629 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-5587694075629 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (62125404860787 / 100000000000000 : ℝ)) / 2) ≤ (-11860727930787 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-11860727930787 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (7456602981689 / 12500000000000 : ℝ)) / 2) ≤ (-51300431671993 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-51300431671993 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (5636253868599 / 10000000000000 : ℝ)) / 2) ≤ (-3534488750387 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-3534488750387 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (52131578158743 / 100000000000000 : ℝ)) / 2) ≤ (-3175687617663 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-3175687617663 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (23423230518473 / 50000000000000 : ℝ)) / 2) ≤ (-2267661303611 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-2267661303611 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (40388128089627 / 100000000000000 : ℝ)) / 2) ≤ (-84212623287347 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-84212623287347 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (16284786148151 / 50000000000000 : ℝ)) / 2) ≤ (-19857183928383 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-19857183928383 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (1143559870643 / 5000000000000 : ℝ)) / 2) ≤ (-23942934030741 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-23942934030741 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((43082559672831 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (1550014300029 / 20000000000000 : ℝ)) / 2) ≤ (-39105299659657 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-39105299659657 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (43082559672831 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_577 : Uρ (2156723943323 / 3200000000000 : ℝ) ≤ (-67576200340573673115391469 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (66752166667321 / 100000000000000 : ℝ)) / 2) ≤ (-5052247516797 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-5052247516797 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (66511770806259 / 100000000000000 : ℝ)) / 2) ≤ (-8155345356349 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-8155345356349 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (66029796655413 / 100000000000000 : ℝ)) / 2) ≤ (-20748962512287 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-20748962512287 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (16306451806937 / 25000000000000 : ℝ)) / 2) ≤ (-21353389244857 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-21353389244857 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (63992989910603 / 100000000000000 : ℝ)) / 2) ≤ (-44574702350297 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-44574702350297 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (62206785804037 / 100000000000000 : ℝ)) / 2) ≤ (-47312416553517 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-47312416553517 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (59734535904253 / 100000000000000 : ℝ)) / 2) ≤ (-25582265801173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-25582265801173 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (56444938780583 / 100000000000000 : ℝ)) / 2) ≤ (-11281598619421 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-11281598619421 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (26107678851227 / 50000000000000 : ℝ)) / 2) ≤ (-6335826382699 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-6335826382699 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (9386591762977 / 20000000000000 : ℝ)) / 2) ≤ (-72392151986107 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-72392151986107 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (40480039948559 / 100000000000000 : ℝ)) / 2) ≤ (-84011991149323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-84011991149323 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (8168240096889 / 25000000000000 : ℝ)) / 2) ≤ (-3094913622253 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-3094913622253 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (1437756750453 / 6250000000000 : ℝ)) / 2) ≤ (-29840249789637 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-29840249789637 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((2156723943323 / 3200000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (4049781136529 / 50000000000000 : ℝ)) / 2) ≤ (-77698761319607 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-77698761319607 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2156723943323 / 3200000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_578 : Uρ (43186398060089 / 64000000000000 : ℝ) ≤ (-421185040792104226047837 / 625000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (33416645497659 / 50000000000000 : ℝ)) / 2) ≤ (-1259266380449 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-1259266380449 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (33296449216259 / 50000000000000 : ℝ)) / 2) ≤ (-20327416054799 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-20327416054799 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (8263866767843 / 12500000000000 : ℝ)) / 2) ≤ (-1292973161143 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-1292973161143 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (6530697102949 / 10000000000000 : ℝ)) / 2) ≤ (-2129124106141 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-2129124106141 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1601855473753 / 2500000000000 : ℝ)) / 2) ≤ (-11112003252549 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-11112003252549 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (12457633215253 / 20000000000000 : ℝ)) / 2) ≤ (-9436418397933 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-9436418397933 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (3738515397091 / 6250000000000 : ℝ)) / 2) ≤ (-51028817304263 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-51028817304263 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (56527335182903 / 100000000000000 : ℝ)) / 2) ≤ (-14066093998323 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-14066093998323 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (52299128872207 / 100000000000000 : ℝ)) / 2) ≤ (-63203024569743 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-63203024569743 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (470194374347 / 1000000000000 : ℝ)) / 2) ≤ (-72219460786213 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-72219460786213 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (20285952898571 / 50000000000000 : ℝ)) / 2) ≤ (-41905906963107 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-41905906963107 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (32776223143187 / 100000000000000 : ℝ)) / 2) ≤ (-1975786747663 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-1975786747663 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (23136539530419 / 100000000000000 : ℝ)) / 2) ≤ (-23801872406357 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-23801872406357 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((43186398060089 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (1687072872111 / 20000000000000 : ℝ)) / 2) ≤ (-154416273762119 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-154416273762119 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (43186398060089 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_579 : Uρ (21619158626859 / 32000000000000 : ℝ) ≤ (-16801255533237353403494269 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6691441532189 / 10000000000000 : ℝ)) / 2) ≤ (-10043803887999 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-10043803887999 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (66674026049319 / 100000000000000 : ℝ)) / 2) ≤ (-40533085846779 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-40533085846779 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (529536572771 / 800000000000 : ℝ)) / 2) ≤ (-20626253943977 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-20626253943977 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (65388134731801 / 100000000000000 : ℝ)) / 2) ≤ (-1326823129251 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-1326823129251 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (12831089544633 / 20000000000000 : ℝ)) / 2) ≤ (-22160742088233 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-22160742088233 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (62369545680097 / 100000000000000 : ℝ)) / 2) ≤ (-47051937584689 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-47051937584689 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (29948977603837 / 50000000000000 : ℝ)) / 2) ≤ (-50893288266931 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-50893288266931 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (3538107994317 / 6250000000000 : ℝ)) / 2) ≤ (-11224193614841 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-11224193614841 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (52382891708177 / 100000000000000 : ℝ)) / 2) ≤ (-63048033758837 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-63048033758837 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (9421179400381 / 20000000000000 : ℝ)) / 2) ≤ (-18011771718789 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-18011771718789 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (40663725947209 / 100000000000000 : ℝ)) / 2) ≤ (-83612089334259 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-83612089334259 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (32879361744103 / 100000000000000 : ℝ)) / 2) ≤ (-19708443634641 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-19708443634641 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (4653700032441 / 20000000000000 : ℝ)) / 2) ≤ (-29664932089353 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-29664932089353 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((21619158626859 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (875905228309 / 10000000000000 : ℝ)) / 2) ≤ (-76736330575169 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-76736330575169 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (21619158626859 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_580 : Uρ (43290236447347 / 64000000000000 : ℝ) ≤ (-33511134503282609189144367 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (66995539647041 / 100000000000000 : ℝ)) / 2) ≤ (-40054053910223 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-40054053910223 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (33377576828349 / 50000000000000 : ℝ)) / 2) ≤ (-1616459505293 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-1616459505293 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (66273209016431 / 100000000000000 : ℝ)) / 2) ≤ (-41130024849663 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-41130024849663 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (65469298335053 / 100000000000000 : ℝ)) / 2) ≤ (-21167176073073 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-21167176073073 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (64236676230747 / 100000000000000 : ℝ)) / 2) ≤ (-55243894303 / 125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-55243894303 / 125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (62450924618147 / 100000000000000 : ℝ)) / 2) ≤ (-23460976446719 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-23460976446719 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (29989831236713 / 50000000000000 : ℝ)) / 2) ≤ (-25378971990827 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-25378971990827 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (28346058487559 / 50000000000000 : ℝ)) / 2) ≤ (-55977768722083 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-55977768722083 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (52466646250279 / 100000000000000 : ℝ)) / 2) ≤ (-62893290575771 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-62893290575771 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (1474760550663 / 3125000000000 : ℝ)) / 2) ≤ (-14375005803963 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-14375005803963 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (40755500707631 / 100000000000000 : ℝ)) / 2) ≤ (-41706407554099 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-41706407554099 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (3298237735503 / 10000000000000 : ℝ)) / 2) ≤ (-98295872473317 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-98295872473317 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (23399997869163 / 100000000000000 : ℝ)) / 2) ≤ (-29578017119751 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-29578017119751 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((43290236447347 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (9071922840439 / 100000000000000 : ℝ)) / 2) ≤ (-610250942377 / 400000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-610250942377 / 400000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (43290236447347 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_581 : Uρ (2708884727561 / 4000000000000 : ℝ) ≤ (-33420598916386471960832197 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (67076663970777 / 100000000000000 : ℝ)) / 2) ≤ (-4991629861663 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-4991629861663 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (66836281254689 / 100000000000000 : ℝ)) / 2) ≤ (-1259063659581 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-1259063659581 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (66354346403033 / 100000000000000 : ℝ)) / 2) ≤ (-41007691674019 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-41007691674019 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (65550461839613 / 100000000000000 : ℝ)) / 2) ≤ (-21105258885693 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-21105258885693 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (32158952236937 / 50000000000000 : ℝ)) / 2) ≤ (-44068906402833 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-44068906402833 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (12506460578603 / 20000000000000 : ℝ)) / 2) ≤ (-9358427494503 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-9358427494503 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (12012273631439 / 20000000000000 : ℝ)) / 2) ≤ (-25311391970921 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-25311391970921 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (2270980095879 / 4000000000000 : ℝ)) / 2) ≤ (-2791738866097 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-2791738866097 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (6568799067271 / 12500000000000 : ℝ)) / 2) ≤ (-62738794206197 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-62738794206197 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (47278759396563 / 100000000000000 : ℝ)) / 2) ≤ (-71703285994601 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-71703285994601 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (816944607687 / 2000000000000 : ℝ)) / 2) ≤ (-83213989001069 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-83213989001069 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (33085271124807 / 100000000000000 : ℝ)) / 2) ≤ (-490251472731 / 500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-490251472731 / 500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (2941380051517 / 12500000000000 : ℝ)) / 2) ≤ (-117966353473263 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-117966353473263 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((2708884727561 / 4000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (9375059107561 / 100000000000000 : ℝ)) / 2) ≤ (-151683195914053 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-151683195914053 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2708884727561 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_582 : Uρ (8678814966921 / 12800000000000 : ℝ) ≤ (-66661681920747107137891783 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (67157788293103 / 100000000000000 : ℝ)) / 2) ≤ (-39812170146789 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-39812170146789 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (2676696353733 / 4000000000000 : ℝ)) / 2) ≤ (-10042183477811 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-10042183477811 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (33217741878153 / 50000000000000 : ℝ)) / 2) ≤ (-1022137699867 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-1022137699867 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (8203953155731 / 12500000000000 : ℝ)) / 2) ≤ (-42086836631393 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-42086836631393 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (32199566226773 / 50000000000000 : ℝ)) / 2) ≤ (-43942856654139 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-43942856654139 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (12522736101457 / 20000000000000 : ℝ)) / 2) ≤ (-9332498176053 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-9332498176053 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (15035768066357 / 25000000000000 : ℝ)) / 2) ≤ (-25243903821501 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-25243903821501 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (11371376838097 / 20000000000000 : ℝ)) / 2) ≤ (-27845996630771 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-27845996630771 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (26317065305623 / 50000000000000 : ℝ)) / 2) ≤ (-12516908767977 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-12516908767977 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (47365162431091 / 100000000000000 : ℝ)) / 2) ≤ (-35765928290697 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-35765928290697 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (20469457640207 / 50000000000000 : ℝ)) / 2) ≤ (-83015608784003 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-83015608784003 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (8297011046669 / 25000000000000 : ℝ)) / 2) ≤ (-19561095744997 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-19561095744997 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (184856526199 / 781250000000 : ℝ)) / 2) ≤ (-7351409695297 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-7351409695297 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((8678814966921 / 12800000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (9669376641751 / 100000000000000 : ℝ)) / 2) ≤ (-150831249111479 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-150831249111479 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (8678814966921 / 12800000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_583 : Uρ (21722997014117 / 32000000000000 : ℝ) ≤ (-66483612614407083173664069 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (8404864076753 / 12500000000000 : ℝ)) / 2) ≤ (-39691447317507 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-39691447317507 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (66998536422641 / 100000000000000 : ℝ)) / 2) ≤ (-20023788844623 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-20023788844623 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (6651662107637 / 10000000000000 : ℝ)) / 2) ≤ (-40763473446653 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-40763473446653 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (65712788554121 / 100000000000000 : ℝ)) / 2) ≤ (-20981654173611 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-20981654173611 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (64480360170759 / 100000000000000 : ℝ)) / 2) ≤ (-2738560362139 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-2738560362139 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (6269505746353 / 10000000000000 : ℝ)) / 2) ≤ (-23266506338381 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-23266506338381 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (30112387402269 / 50000000000000 : ℝ)) / 2) ≤ (-12588253645681 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-12588253645681 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (14234815592849 / 25000000000000 : ℝ)) / 2) ≤ (-55549415931397 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-55549415931397 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (3294866281791 / 6250000000000 : ℝ)) / 2) ≤ (-62430538670707 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-62430538670707 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (1898061873087 / 4000000000000 : ℝ)) / 2) ≤ (-35680369784739 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-35680369784739 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (41030555696019 / 100000000000000 : ℝ)) / 2) ≤ (-10352209030751 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-10352209030751 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (8322674414641 / 25000000000000 : ℝ)) / 2) ≤ (-24390354853001 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-24390354853001 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (23791790063931 / 100000000000000 : ℝ)) / 2) ≤ (-23456129180343 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-23456129180343 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((21722997014117 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (4977828797081 / 50000000000000 : ℝ)) / 2) ≤ (-75002253546353 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-75002253546353 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (21722997014117 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_584 : Uρ (43497913221863 / 64000000000000 : ℝ) ≤ (-4144180989802573872404027 / 6250000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (13464007386709 / 20000000000000 : ℝ)) / 2) ≤ (-39570870053569 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-39570870053569 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (67079663992671 / 100000000000000 : ℝ)) / 2) ≤ (-1996328404243 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-1996328404243 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (16649439590837 / 25000000000000 : ℝ)) / 2) ≤ (-40641587666273 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-40641587666273 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (13158790352959 / 20000000000000 : ℝ)) / 2) ≤ (-4183993254133 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-4183993254133 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (32280793813251 / 50000000000000 : ℝ)) / 2) ≤ (-8738246684503 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-8738246684503 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (6277643376431 / 10000000000000 : ℝ)) / 2) ≤ (-23201851211901 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-23201851211901 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (60306475780901 / 100000000000000 : ℝ)) / 2) ≤ (-5021840426067 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-5021840426067 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (28510818477683 / 50000000000000 : ℝ)) / 2) ≤ (-55407044724733 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-55407044724733 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (26400791134647 / 50000000000000 : ℝ)) / 2) ≤ (-3892298618537 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-3892298618537 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (47537912686423 / 100000000000000 : ℝ)) / 2) ≤ (-35594966877739 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-35594966877739 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (41122151928537 / 100000000000000 : ℝ)) / 2) ≤ (-10327522149223 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-10327522149223 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (33393232643359 / 100000000000000 : ℝ)) / 2) ≤ (-97318111077603 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-97318111077603 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (37377362077 / 156250000000 : ℝ)) / 2) ≤ (-116940598932977 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-116940598932977 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((43497913221863 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (10234576383357 / 100000000000000 : ℝ)) / 2) ≤ (-9325056806911 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-9325056806911 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (43497913221863 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_585 : Uρ (10887458103873 / 16000000000000 : ℝ) ≤ (-66131449443726342546613293 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (67401161251671 / 100000000000000 : ℝ)) / 2) ≤ (-7890087600871 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-7890087600871 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (8395098944181 / 12500000000000 : ℝ)) / 2) ≤ (-39805704743641 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-39805704743641 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (66678895617359 / 100000000000000 : ℝ)) / 2) ≤ (-4051985029121 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-4051985029121 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (8234389359779 / 12500000000000 : ℝ)) / 2) ≤ (-10429177209393 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-10429177209393 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (64642814821763 / 100000000000000 : ℝ)) / 2) ≤ (-21782829569977 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-21782829569977 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (62857809412169 / 100000000000000 : ℝ)) / 2) ≤ (-23137279842449 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-23137279842449 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (30194087600431 / 50000000000000 : ℝ)) / 2) ≤ (-78256212779 / 156250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-78256212779 / 156250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (57104007957961 / 100000000000000 : ℝ)) / 2) ≤ (-11052975807497 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-11052975807497 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (26442647965901 / 50000000000000 : ℝ)) / 2) ≤ (-12424652143903 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-12424652143903 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (47624260109683 / 100000000000000 : ℝ)) / 2) ≤ (-71019437943301 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-71019437943301 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (10303426068139 / 25000000000000 : ℝ)) / 2) ≤ (-82423121451513 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-82423121451513 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (33495650229179 / 100000000000000 : ℝ)) / 2) ≤ (-48537774129489 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-48537774129489 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (12025403678301 / 50000000000000 : ℝ)) / 2) ≤ (-11660238798583 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-11660238798583 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((10887458103873 / 16000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (5253359674621 / 50000000000000 : ℝ)) / 2) ≤ (-148418661217259 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-148418661217259 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (10887458103873 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_586 : Uρ (43601751609121 / 64000000000000 : ℝ) ≤ (-32978600582776434491542373 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (67482285568407 / 100000000000000 : ℝ)) / 2) ≤ (-39330150820509 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-39330150820509 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (13448383821001 / 20000000000000 : ℝ)) / 2) ≤ (-4960623414053 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-4960623414053 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2670401313541 / 4000000000000 : ℝ)) / 2) ≤ (-40398260960453 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-40398260960453 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (65956277894789 / 100000000000000 : ℝ)) / 2) ≤ (-10398409215299 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-10398409215299 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (809050521969 / 1250000000000 : ℝ)) / 2) ≤ (-169688447457 / 390625000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-169688447457 / 390625000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (62939184409641 / 100000000000000 : ℝ)) / 2) ≤ (-46145584025263 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-46145584025263 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (7558734133841 / 12500000000000 : ℝ)) / 2) ≤ (-49949729840167 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-49949729840167 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (1787074231083 / 3125000000000 : ℝ)) / 2) ≤ (-55122918268277 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-55122918268277 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (52969001534577 / 100000000000000 : ℝ)) / 2) ≤ (-61969986345457 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-61969986345457 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (47710589197053 / 100000000000000 : ℝ)) / 2) ≤ (-2833970037763 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-2833970037763 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (41305213019909 / 100000000000000 : ℝ)) / 2) ≤ (-82226502860669 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-82226502860669 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (6719590297927 / 20000000000000 : ℝ)) / 2) ≤ (-12104215694881 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-12104215694881 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (1511230236271 / 6250000000000 : ℝ)) / 2) ≤ (-116265987444861 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-116265987444861 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((43601751609121 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (1346575003383 / 12500000000000 : ℝ)) / 2) ≤ (-1153563999771 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-1153563999771 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (43601751609121 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_587 : Uρ (174614683211 / 256000000000 : ℝ) ≤ (-65784086985985354805796897 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((174614683211 / 256000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (33781704941879 / 50000000000000 : ℝ)) / 2) ≤ (-19605004076969 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-19605004076969 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((174614683211 / 256000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (67323046647377 / 100000000000000 : ℝ)) / 2) ≤ (-19782207719661 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-19782207719661 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((174614683211 / 256000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (16710292506741 / 25000000000000 : ℝ)) / 2) ≤ (-40276819314307 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-40276819314307 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((174614683211 / 256000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (8254680101853 / 12500000000000 : ℝ)) / 2) ≤ (-2591919764927 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-2591919764927 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((174614683211 / 256000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (64805268434751 / 100000000000000 : ℝ)) / 2) ≤ (-5414372906697 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-5414372906697 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((174614683211 / 256000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (15755139689811 / 25000000000000 : ℝ)) / 2) ≤ (-46016775011811 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-46016775011811 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((174614683211 / 256000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (30275784698387 / 50000000000000 : ℝ)) / 2) ≤ (-49815664751301 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-49815664751301 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((174614683211 / 256000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (28634369640419 / 50000000000000 : ℝ)) / 2) ≤ (-27490580909203 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-27490580909203 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((174614683211 / 256000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (53052699115767 / 100000000000000 : ℝ)) / 2) ≤ (-482944953003 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-482944953003 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((174614683211 / 256000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (9559380009577 / 20000000000000 : ℝ)) / 2) ≤ (-8834921447011 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-8834921447011 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((174614683211 / 256000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (41396678459713 / 100000000000000 : ℝ)) / 2) ≤ (-82030319279827 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-82030319279827 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((174614683211 / 256000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (33700137484091 / 100000000000000 : ℝ)) / 2) ≤ (-96592637645333 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-96592637645333 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((174614683211 / 256000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (24308147668059 / 100000000000000 : ℝ)) / 2) ≤ (-4637254891667 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-4637254891667 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((174614683211 / 256000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (1379083897267 / 12500000000000 : ℝ)) / 2) ≤ (-918200712237 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-918200712237 / 625000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (174614683211 / 256000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_588 : Uρ (43705589996379 / 64000000000000 : ℝ) ≤ (-32806024924189971373562741 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (67644534197729 / 100000000000000 : ℝ)) / 2) ≤ (-19545004828899 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-19545004828899 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (16851043545149 / 25000000000000 : ℝ)) / 2) ≤ (-19721994386861 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-19721994386861 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (66922307182797 / 100000000000000 : ℝ)) / 2) ≤ (-40155524994387 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-40155524994387 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (66118603638693 / 100000000000000 : ℝ)) / 2) ≤ (-41347946598487 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-41347946598487 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (64886494854427 / 100000000000000 : ℝ)) / 2) ≤ (-43189880859147 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-43189880859147 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (31550966231743 / 50000000000000 : ℝ)) / 2) ≤ (-45888132213137 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-45888132213137 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (1515831604631 / 2500000000000 : ℝ)) / 2) ≤ (-12420445104949 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-12420445104949 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (57351099631803 / 100000000000000 : ℝ)) / 2) ≤ (-27419804545913 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-27419804545913 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (26568194356639 / 50000000000000 : ℝ)) / 2) ≤ (-30832081425109 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-30832081425109 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (9576638552159 / 20000000000000 : ℝ)) / 2) ≤ (-70509798664727 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-70509798664727 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (41488100878397 / 100000000000000 : ℝ)) / 2) ≤ (-8183456858447 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-8183456858447 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (16901104628957 / 50000000000000 : ℝ)) / 2) ≤ (-96352279248873 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-96352279248873 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (4887241105203 / 20000000000000 : ℝ)) / 2) ≤ (-57799259042741 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-57799259042741 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((43705589996379 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (11287334381023 / 100000000000000 : ℝ)) / 2) ≤ (-73092597852341 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-73092597852341 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (43705589996379 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_589 : Uρ (5469688648751 / 8000000000000 : ℝ) ≤ (-13088207722544622895417283 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (33862829255163 / 50000000000000 : ℝ)) / 2) ≤ (-19485077493247 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-19485077493247 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (8435662713087 / 12500000000000 : ℝ)) / 2) ≤ (-39323706966273 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-39323706966273 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3350172215307 / 5000000000000 : ℝ)) / 2) ≤ (-10008594410903 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-10008594410903 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (66199766366749 / 100000000000000 : ℝ)) / 2) ≤ (-2061266378477 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-2061266378477 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (8120965127189 / 12500000000000 : ℝ)) / 2) ≤ (-5383116871579 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-5383116871579 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (63183305524859 / 100000000000000 : ℝ)) / 2) ≤ (-45759655199519 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-45759655199519 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (60714957442333 / 100000000000000 : ℝ)) / 2) ≤ (-9909615271101 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-9909615271101 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (57433456462761 / 100000000000000 : ℝ)) / 2) ≤ (-27349129747567 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-27349129747567 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (53220070364773 / 100000000000000 : ℝ)) / 2) ≤ (-61511612160809 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-61511612160809 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (47969467433669 / 100000000000000 : ℝ)) / 2) ≤ (-3517026552121 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-3517026552121 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (20789740279869 / 50000000000000 : ℝ)) / 2) ≤ (-16327849733361 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-16327849733361 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (211901049017 / 625000000000 : ℝ)) / 2) ≤ (-24028161290791 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-24028161290791 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (3070482963053 / 12500000000000 : ℝ)) / 2) ≤ (-14408425118059 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-14408425118059 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((5469688648751 / 8000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (5768473880837 / 50000000000000 : ℝ)) / 2) ≤ (-145474338021193 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-145474338021193 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (5469688648751 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_590 : Uρ (43809428383637 / 64000000000000 : ℝ) ≤ (-32635503603063058698880607 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4237923926347 / 6250000000000 : ℝ)) / 2) ≤ (-19425221897837 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-19425221897837 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (16891607304927 / 25000000000000 : ℝ)) / 2) ≤ (-4900446208611 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-4900446208611 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (67084581397113 / 100000000000000 : ℝ)) / 2) ≤ (-9978344226549 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-9978344226549 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (13256185799869 / 20000000000000 : ℝ)) / 2) ≤ (-10275714695683 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-10275714695683 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (65048946924969 / 100000000000000 : ℝ)) / 2) ≤ (-42940145202433 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-42940145202433 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (12652935589169 / 20000000000000 : ℝ)) / 2) ≤ (-45631343542901 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-45631343542901 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (30398324587113 / 50000000000000 : ℝ)) / 2) ≤ (-49414552070283 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-49414552070283 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (1797369055901 / 3125000000000 : ℝ)) / 2) ≤ (-3409819527347 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-3409819527347 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (53303744107677 / 100000000000000 : ℝ)) / 2) ≤ (-61359301137907 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-61359301137907 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (48055724163669 / 100000000000000 : ℝ)) / 2) ≤ (-35085783774289 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-35085783774289 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (41670817784891 / 100000000000000 : ℝ)) / 2) ≤ (-10180544679447 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-10180544679447 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (17003007128309 / 50000000000000 : ℝ)) / 2) ≤ (-23968432560779 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-23968432560779 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (12345564201281 / 50000000000000 : ℝ)) / 2) ≤ (-11493799752797 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-11493799752797 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((43809428383637 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (5890916142769 / 50000000000000 : ℝ)) / 2) ≤ (-144778554904263 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-144778554904263 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (43809428383637 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_591 : Uρ (21930673788633 / 32000000000000 : ℝ) ≤ (-65101913924676510561694767 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (33943953565707 / 50000000000000 : ℝ)) / 2) ≤ (-38730875742217 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-38730875742217 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (67647556725667 / 100000000000000 : ℝ)) / 2) ≤ (-4885447066841 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-4885447066841 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (8395714806979 / 12500000000000 : ℝ)) / 2) ≤ (-39792522427647 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-39792522427647 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (6636209153683 / 10000000000000 : ℝ)) / 2) ≤ (-20490269935081 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-20490269935081 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (32565086288877 / 50000000000000 : ℝ)) / 2) ≤ (-42815511158423 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-42815511158423 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (63346049728911 / 100000000000000 : ℝ)) / 2) ≤ (-45503196816891 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-45503196816891 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (30439169693529 / 50000000000000 : ℝ)) / 2) ≤ (-2464060353899 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-2464060353899 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (57598159625051 / 100000000000000 : ℝ)) / 2) ≤ (-54416167330909 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-54416167330909 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (26693704989587 / 50000000000000 : ℝ)) / 2) ≤ (-61207229007141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-61207229007141 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (48141963047239 / 100000000000000 : ℝ)) / 2) ≤ (-35001453514771 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-35001453514771 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (20881056416211 / 50000000000000 : ℝ)) / 2) ≤ (-81249892815887 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-81249892815887 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (34107749504441 / 100000000000000 : ℝ)) / 2) ≤ (-47817764702019 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-47817764702019 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (24818005673633 / 100000000000000 : ℝ)) / 2) ≤ (-7163142813707 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-7163142813707 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((21930673788633 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (12022276925603 / 100000000000000 : ℝ)) / 2) ≤ (-72048478922801 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-72048478922801 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (21930673788633 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_592 : Uρ (8782653354179 / 12800000000000 : ℝ) ≤ (-64933720854900674375321999 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (13593806287983 / 20000000000000 : ℝ)) / 2) ≤ (-7722290096847 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-7722290096847 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (67728684222603 / 100000000000000 : ℝ)) / 2) ≤ (-7792745443641 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-7792745443641 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (33623427741207 / 50000000000000 : ℝ)) / 2) ≤ (-39671813854753 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-39671813854753 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (66443253979553 / 100000000000000 : ℝ)) / 2) ≤ (-20429185232639 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-20429185232639 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (32605698988409 / 50000000000000 : ℝ)) / 2) ≤ (-1334094764123 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-1334094764123 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (63427420876513 / 100000000000000 : ℝ)) / 2) ≤ (-5671901824593 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-5671901824593 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (30480014043469 / 50000000000000 : ℝ)) / 2) ≤ (-12287010223607 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-12287010223607 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (57680505986363 / 100000000000000 : ℝ)) / 2) ≤ (-10855084717927 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-10855084717927 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (53471068016213 / 100000000000000 : ℝ)) / 2) ≤ (-15263848749497 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-15263848749497 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (48228184180117 / 100000000000000 : ℝ)) / 2) ≤ (-69834548338513 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-69834548338513 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (41853365978339 / 100000000000000 : ℝ)) / 2) ≤ (-10131981593627 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-10131981593627 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (34209374577979 / 100000000000000 : ℝ)) / 2) ≤ (-95398037620639 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-95398037620639 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (4988900285889 / 20000000000000 : ℝ)) / 2) ≤ (-14285530138677 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-14285530138677 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((8782653354179 / 12800000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (6129271471179 / 50000000000000 : ℝ)) / 2) ≤ (-71714371415963 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-71714371415963 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (8782653354179 / 12800000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_593 : Uρ (10991296491131 / 16000000000000 : ℝ) ≤ (-64766393390687885537074881 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3402507787353 / 5000000000000 : ℝ)) / 2) ≤ (-4811520960133 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-4811520960133 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (67809811710551 / 100000000000000 : ℝ)) / 2) ≤ (-3884402137497 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-3884402137497 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (4207999529811 / 6250000000000 : ℝ)) / 2) ≤ (-39551250835583 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-39551250835583 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (66524416327861 / 100000000000000 : ℝ)) / 2) ≤ (-20368175101437 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-20368175101437 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (16323155780777 / 25000000000000 : ℝ)) / 2) ≤ (-42566708695763 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-42566708695763 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (15877197847773 / 25000000000000 : ℝ)) / 2) ≤ (-22623698229683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-22623698229683 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (30520857639969 / 50000000000000 : ℝ)) / 2) ≤ (-49015053037431 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-49015053037431 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (57762848887631 / 100000000000000 : ℝ)) / 2) ≤ (-13533720157683 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-13533720157683 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (53554718255509 / 100000000000000 : ℝ)) / 2) ≤ (-60903798343747 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-60903798343747 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (9662877531467 / 20000000000000 : ℝ)) / 2) ≤ (-6966649033551 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-6966649033551 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (41944577496119 / 100000000000000 : ℝ)) / 2) ≤ (-80862235192249 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-80862235192249 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (8577722614051 / 25000000000000 : ℝ)) / 2) ≤ (-95161249926053 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-95161249926053 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (25070621444891 / 100000000000000 : ℝ)) / 2) ≤ (-113959843981011 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-113959843981011 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((10991296491131 / 16000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (12490867455297 / 100000000000000 : ℝ)) / 2) ≤ (-142773179493041 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-142773179493041 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (10991296491131 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_594 : Uρ (44017105158153 / 64000000000000 : ℝ) ≤ (-16149974956767753370230233 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (8516410006607 / 12500000000000 : ℝ)) / 2) ≤ (-38373026993253 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-38373026993253 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (67890939189541 / 100000000000000 : ℝ)) / 2) ≤ (-3872445866191 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-3872445866191 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (4213070589977 / 6250000000000 : ℝ)) / 2) ≤ (-39430833019477 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-39430833019477 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (66605578582099 / 100000000000000 : ℝ)) / 2) ≤ (-1015361967977 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-1015361967977 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (65373848017567 / 100000000000000 : ℝ)) / 2) ≤ (-42442539504141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-42442539504141 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (1589754031877 / 2500000000000 : ℝ)) / 2) ≤ (-4511974198329 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-4511974198329 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (611234009721 / 1000000000000 : ℝ)) / 2) ≤ (-48882243026753 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-48882243026753 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (57845188343631 / 100000000000000 : ℝ)) / 2) ≤ (-53994537873769 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-53994537873769 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (6704795091693 / 12500000000000 : ℝ)) / 2) ≤ (-12150487656303 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-12150487656303 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (4840057357323 / 10000000000000 : ℝ)) / 2) ≤ (-13899746377461 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-13899746377461 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (8407149531349 / 20000000000000 : ℝ)) / 2) ≤ (-16133807623739 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-16133807623739 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (34412298105491 / 100000000000000 : ℝ)) / 2) ≤ (-18985032282177 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-18985032282177 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (1259818568113 / 5000000000000 : ℝ)) / 2) ≤ (-7102317018343 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-7102317018343 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((44017105158153 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (12719466444169 / 100000000000000 : ℝ)) / 2) ≤ (-142129601979349 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-142129601979349 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (44017105158153 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_595 : Uρ (22034512175891 / 32000000000000 : ℝ) ≤ (-64434211016416232240795473 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (13642480871461 / 20000000000000 : ℝ)) / 2) ≤ (-4781753510321 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-4781753510321 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (67972066659607 / 100000000000000 : ℝ)) / 2) ≤ (-19302519368571 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-19302519368571 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (67490266370499 / 100000000000000 : ℝ)) / 2) ≤ (-39310560057041 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-39310560057041 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (6668674074261 / 10000000000000 : ℝ)) / 2) ≤ (-8098551130271 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-8098551130271 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (65455072661133 / 100000000000000 : ℝ)) / 2) ≤ (-42318524492747 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-42318524492747 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (63671530530893 / 100000000000000 : ℝ)) / 2) ≤ (-22496125374341 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-22496125374341 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (30602542584717 / 50000000000000 : ℝ)) / 2) ≤ (-4874961038411 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-4874961038411 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (11585504873811 / 20000000000000 : ℝ)) / 2) ≤ (-53854394740863 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-53854394740863 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (5372199548657 / 10000000000000 : ℝ)) / 2) ≤ (-60601314052161 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-60601314052161 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (48486742021447 / 100000000000000 : ℝ)) / 2) ≤ (-34665635933687 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-34665635933687 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (5265859591091 / 12500000000000 : ℝ)) / 2) ≤ (-40238129758561 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-40238129758561 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (34513598479833 / 100000000000000 : ℝ)) / 2) ≤ (-3787590688891 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-3787590688891 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (6330439173841 / 25000000000000 : ℝ)) / 2) ≤ (-22663181033671 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-22663181033671 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((22034512175891 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (2588907457483 / 20000000000000 : ℝ)) / 2) ≤ (-8843587577709 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-8843587577709 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (22034512175891 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_596 : Uρ (44120943545411 / 64000000000000 : ℝ) ≤ (-32134650038942768634843931 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (34146764330207 / 50000000000000 : ℝ)) / 2) ≤ (-4766896326497 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-4766896326497 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (68053194120779 / 100000000000000 : ℝ)) / 2) ≤ (-19242880630003 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-19242880630003 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (67571403269691 / 100000000000000 : ℝ)) / 2) ≤ (-39190431600141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-39190431600141 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (66767902809737 / 100000000000000 : ℝ)) / 2) ≤ (-8074236127697 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-8074236127697 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (65536297054737 / 100000000000000 : ℝ)) / 2) ≤ (-8438932655739 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-8438932655739 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (63752899160937 / 100000000000000 : ℝ)) / 2) ≤ (-22432461168661 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-22432461168661 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (61286767877917 / 100000000000000 : ℝ)) / 2) ≤ (-9723430926631 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-9723430926631 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (58009856978509 / 100000000000000 : ℝ)) / 2) ≤ (-10742890131333 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-10742890131333 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (5380562255061 / 10000000000000 : ℝ)) / 2) ≤ (-60450424900299 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-60450424900299 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (48572893094951 / 100000000000000 : ℝ)) / 2) ≤ (-69164109181829 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-69164109181829 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (8443592995629 / 20000000000000 : ℝ)) / 2) ≤ (-40141948695891 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-40141948695891 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (8653698130263 / 25000000000000 : ℝ)) / 2) ≤ (-47227531281493 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-47227531281493 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (25446782833511 / 100000000000000 : ℝ)) / 2) ≤ (-28249080543813 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-28249080543813 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((44120943545411 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (13166260922093 / 100000000000000 : ℝ)) / 2) ≤ (-4402375577177 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-4402375577177 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (44120943545411 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_597 : Uρ (276080392119 / 400000000000 : ℝ) ≤ (-32052571068931126634799227 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((276080392119 / 400000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (68374652962187 / 100000000000000 : ℝ)) / 2) ≤ (-760329084913 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-760329084913 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((276080392119 / 400000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6813432157309 / 10000000000000 : ℝ)) / 2) ≤ (-1918331294553 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-1918331294553 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((276080392119 / 400000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (67652540137321 / 100000000000000 : ℝ)) / 2) ≤ (-4883805912737 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-4883805912737 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((276080392119 / 400000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (66849064783819 / 100000000000000 : ℝ)) / 2) ≤ (-10062438330143 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-10062438330143 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((276080392119 / 400000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (16404380299827 / 25000000000000 : ℝ)) / 2) ≤ (-21035477740261 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-21035477740261 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((276080392119 / 400000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (12766853433521 / 20000000000000 : ℝ)) / 2) ≤ (-22368878166301 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-22368878166301 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((276080392119 / 400000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (61368449103493 / 100000000000000 : ℝ)) / 2) ≤ (-48484875299473 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-48484875299473 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((276080392119 / 400000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (58092186186519 / 100000000000000 : ℝ)) / 2) ≤ (-53574705048343 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-53574705048343 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((276080392119 / 400000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (2694462098073 / 5000000000000 : ℝ)) / 2) ≤ (-12059954014853 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-12059954014853 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((276080392119 / 400000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (48659026886027 / 100000000000000 : ℝ)) / 2) ≤ (-68997242665391 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-68997242665391 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((276080392119 / 400000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (42309012668657 / 100000000000000 : ℝ)) / 2) ≤ (-80091949762253 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-80091949762253 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((276080392119 / 400000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (17357940579503 / 50000000000000 : ℝ)) / 2) ≤ (-18844208538101 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-18844208538101 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((276080392119 / 400000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (12785727522661 / 50000000000000 : ℝ)) / 2) ≤ (-112678303318509 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-112678303318509 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((276080392119 / 400000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (13384803692037 / 100000000000000 : ℝ)) / 2) ≤ (-140264939451433 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-140264939451433 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (276080392119 / 400000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_598 : Uρ (44224781932669 / 64000000000000 : ℝ) ≤ (-799271426593582936082721 / 1250000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (17113944315657 / 25000000000000 : ℝ)) / 2) ≤ (-18948939324477 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-18948939324477 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (17053862254143 / 25000000000000 : ℝ)) / 2) ≤ (-38247632292073 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-38247632292073 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (33866838486751 / 50000000000000 : ℝ)) / 2) ≤ (-1558024272667 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-1558024272667 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (13386045333039 / 20000000000000 : ℝ)) / 2) ≤ (-40128473339029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-40128473339029 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (6569874509577 / 10000000000000 : ℝ)) / 2) ≤ (-8389480143637 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-8389480143637 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (31957817276639 / 50000000000000 : ℝ)) / 2) ≤ (-8922150463903 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-8922150463903 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (15362532213019 / 25000000000000 : ℝ)) / 2) ≤ (-48352771910567 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-48352771910567 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (14543628001881 / 25000000000000 : ℝ)) / 2) ≤ (-53435157345571 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-53435157345571 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (53972853754691 / 100000000000000 : ℝ)) / 2) ≤ (-6014934882609 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-6014934882609 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (4874514348629 / 10000000000000 : ℝ)) / 2) ≤ (-13766134247461 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-13766134247461 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (42400020061549 / 100000000000000 : ℝ)) / 2) ≤ (-15980082932653 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-15980082932653 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (34816865311791 / 100000000000000 : ℝ)) / 2) ≤ (-18797540583233 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-18797540583233 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (25695778482397 / 100000000000000 : ℝ)) / 2) ≤ (-112361829024221 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-112361829024221 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((44224781932669 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (13600318937529 / 100000000000000 : ℝ)) / 2) ≤ (-34915922437851 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-34915922437851 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (44224781932669 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_599 : Uρ (22138350563149 / 32000000000000 : ℝ) ≤ (-6377899458709889793121613 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (34268450780871 / 50000000000000 : ℝ)) / 2) ≤ (-37779443488443 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-37779443488443 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (13659315290251 / 20000000000000 : ℝ)) / 2) ≤ (-38128780126021 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-38128780126021 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (67814813778349 / 100000000000000 : ℝ)) / 2) ≤ (-19415454900043 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-19415454900043 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (33505694227101 / 50000000000000 : ℝ)) / 2) ≤ (-20003670168287 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-20003670168287 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (32889984372521 / 50000000000000 : ℝ)) / 2) ≤ (-41823998613053 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-41823998613053 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (15999250330081 / 25000000000000 : ℝ)) / 2) ≤ (-44483909884649 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-44483909884649 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (15382951782387 / 25000000000000 : ℝ)) / 2) ≤ (-48220843995847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-48220843995847 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (11651366891177 / 20000000000000 : ℝ)) / 2) ≤ (-53295806980507 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-53295806980507 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (1081129159313 / 2000000000000 : ℝ)) / 2) ≤ (-59999160411479 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-59999160411479 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (12207810746673 / 25000000000000 : ℝ)) / 2) ≤ (-8583049224663 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-8583049224663 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (42490987415749 / 100000000000000 : ℝ)) / 2) ≤ (-39854645072271 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-39854645072271 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (17458872942969 / 50000000000000 : ℝ)) / 2) ≤ (-93755038604291 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-93755038604291 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (25819758182839 / 100000000000000 : ℝ)) / 2) ≤ (-56023440063907 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-56023440063907 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((22138350563149 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (1726618546163 / 12500000000000 : ℝ)) / 2) ≤ (-139071830518069 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-139071830518069 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (22138350563149 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

end Apery
