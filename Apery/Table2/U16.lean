import Apery.Table2.Data

set_option maxHeartbeats 4000000

namespace Apery

lemma U_pt_640 : Uρ (11854766575033 / 16000000000000 : ℝ) ≤ (-53710342503159047732044301 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (14689375736729 / 20000000000000 : ℝ)) / 2) ≤ (-30860478288937 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-30860478288937 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (73206730404301 / 100000000000000 : ℝ)) / 2) ≤ (-15593151394341 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-15593151394341 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (36362747913409 / 50000000000000 : ℝ)) / 2) ≤ (-3184082324783 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-3184082324783 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (35961738537829 / 50000000000000 : ℝ)) / 2) ≤ (-32936413792903 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-32936413792903 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (35347767039591 / 50000000000000 : ℝ)) / 2) ≤ (-8656385258303 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-8656385258303 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (68920589128413 / 100000000000000 : ℝ)) / 2) ≤ (-37092592179753 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-37092592179753 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (33236393502703 / 50000000000000 : ℝ)) / 2) ≤ (-20272781832061 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-20272781832061 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (31616781156849 / 50000000000000 : ℝ)) / 2) ≤ (-45208548239043 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-45208548239043 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (14775915445891 / 25000000000000 : ℝ)) / 2) ≤ (-25657917882433 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-25657917882433 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (337585429341 / 625000000000 : ℝ)) / 2) ≤ (-14777219452643 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-14777219452643 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (47930952176311 / 100000000000000 : ℝ)) / 2) ≤ (-13767704340553 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-13767704340553 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (20429967292823 / 50000000000000 : ℝ)) / 2) ≤ (-5048627537273 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-5048627537273 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (32828742541227 / 100000000000000 : ℝ)) / 2) ≤ (-95263962110557 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-95263962110557 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (11917326480609 / 50000000000000 : ℝ)) / 2) ≤ (-3526209586269 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-3526209586269 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((11854766575033 / 16000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (1693053124173 / 12500000000000 : ℝ)) / 2) ≤ (-135044507908137 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-135044507908137 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (11854766575033 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_641 : Uρ (23740009868623 / 32000000000000 : ℝ) ≤ (-26764469752149586909481961 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (73542118999249 / 100000000000000 : ℝ)) / 2) ≤ (-30730890686709 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-30730890686709 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (36650986957801 / 50000000000000 : ℝ)) / 2) ≤ (-31056290364713 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-31056290364713 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (9102593609473 / 12500000000000 : ℝ)) / 2) ≤ (-7927487771283 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-7927487771283 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (72018755500693 / 100000000000000 : ℝ)) / 2) ≤ (-820102081581 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-820102081581 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (70790875121021 / 100000000000000 : ℝ)) / 2) ≤ (-34490913600919 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-34490913600919 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (69016074278761 / 100000000000000 : ℝ)) / 2) ≤ (-1847725008117 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-1847725008117 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (1331371666553 / 2000000000000 : ℝ)) / 2) ≤ (-40402390512011 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-40402390512011 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (63329994379997 / 100000000000000 : ℝ)) / 2) ≤ (-9011609430667 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-9011609430667 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (59201335727521 / 100000000000000 : ℝ)) / 2) ≤ (-10230965718353 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-10230965718353 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (54113691393891 / 100000000000000 : ℝ)) / 2) ≤ (-58932715606959 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-58932715606959 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (24017671904287 / 50000000000000 : ℝ)) / 2) ≤ (-17160008954017 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-17160008954017 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (40972494076343 / 100000000000000 : ℝ)) / 2) ≤ (-40272636377959 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-40272636377959 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (16478596823019 / 50000000000000 : ℝ)) / 2) ≤ (-9497441751319 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-9497441751319 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (599940542379 / 2500000000000 : ℝ)) / 2) ≤ (-14055060307111 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-14055060307111 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((23740009868623 / 32000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (6905653115133 / 50000000000000 : ℝ)) / 2) ≤ (-3358704987137 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-3358704987137 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (23740009868623 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_642 : Uρ (1188524329359 / 1600000000000 : ℝ) ≤ (-53348344530846937981847389 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (36818679656689 / 50000000000000 : ℝ)) / 2) ≤ (-30601470797637 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-30601470797637 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (7339721741713 / 10000000000000 : ℝ)) / 2) ≤ (-30926446760251 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-30926446760251 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (36458000944997 / 50000000000000 : ℝ)) / 2) ≤ (-1578962499883 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-1578962499883 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (3605701691177 / 5000000000000 : ℝ)) / 2) ≤ (-32671927686707 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-32671927686707 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1772155397263 / 2500000000000 : ℝ)) / 2) ≤ (-4294558420303 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-4294558420303 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (69111558751873 / 100000000000000 : ℝ)) / 2) ≤ (-36816599065371 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-36816599065371 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (33332189027473 / 50000000000000 : ℝ)) / 2) ≤ (-20129711622583 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-20129711622583 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (12685284568631 / 20000000000000 : ℝ)) / 2) ≤ (-11226943763969 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-11226943763969 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (7412375219057 / 12500000000000 : ℝ)) / 2) ≤ (-50994086828453 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-50994086828453 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (433709574931 / 800000000000 : ℝ)) / 2) ≤ (-7344609836213 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-7344609836213 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (48139697488729 / 100000000000000 : ℝ)) / 2) ≤ (-4277623796117 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-4277623796117 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (20542482983727 / 50000000000000 : ℝ)) / 2) ≤ (-80313143250069 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-80313143250069 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (8271355052321 / 25000000000000 : ℝ)) / 2) ≤ (-18937199649167 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-18937199649167 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (24159866586647 / 100000000000000 : ℝ)) / 2) ≤ (-28011236854857 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-28011236854857 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((1188524329359 / 1600000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (3518442947431 / 25000000000000 : ℝ)) / 2) ≤ (-66832554649139 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-66832554649139 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1188524329359 / 1600000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_643 : Uρ (23800963305737 / 32000000000000 : ℝ) ≤ (-26584266391250005908207001 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (36866299813019 / 50000000000000 : ℝ)) / 2) ≤ (-30472218188171 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-30472218188171 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (36746230454461 / 50000000000000 : ℝ)) / 2) ≤ (-7699192884357 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-7699192884357 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (36505627434793 / 50000000000000 : ℝ)) / 2) ≤ (-31448719538679 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-31448719538679 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (14441862408921 / 20000000000000 : ℝ)) / 2) ≤ (-32539946601121 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-32539946601121 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (8872694548597 / 12500000000000 : ℝ)) / 2) ≤ (-4277775228767 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-4277775228767 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (8650880318819 / 12500000000000 : ℝ)) / 2) ≤ (-3667888836031 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-3667888836031 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (834502139927 / 1250000000000 : ℝ)) / 2) ≤ (-40116661268899 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-40116661268899 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (63522847719583 / 100000000000000 : ℝ)) / 2) ≤ (-44757731242411 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-44757731242411 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (5939665989743 / 10000000000000 : ℝ)) / 2) ≤ (-6354201197499 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-6354201197499 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (54313685207167 / 100000000000000 : ℝ)) / 2) ≤ (-14645341451041 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-14645341451041 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (964880269261 / 2000000000000 : ℝ)) / 2) ≤ (-34122177223491 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-34122177223491 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (41197350976441 / 100000000000000 : ℝ)) / 2) ≤ (-40040824048203 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-40040824048203 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (33213424831619 / 100000000000000 : ℝ)) / 2) ≤ (-9439869366023 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-9439869366023 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (12160701060829 / 50000000000000 : ℝ)) / 2) ≤ (-111652053955447 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-111652053955447 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((23800963305737 / 32000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (14332064268991 / 100000000000000 : ℝ)) / 2) ≤ (-66497271075113 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-66497271075113 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (23800963305737 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_644 : Uρ (11915720012147 / 16000000000000 : ℝ) ≤ (-827960645997125472864193 / 1562500000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (14765567987447 / 20000000000000 : ℝ)) / 2) ≤ (-15171566213217 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-15171566213217 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (36793852195509 / 50000000000000 : ℝ)) / 2) ≤ (-7666816065019 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-7666816065019 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (73106507814693 / 100000000000000 : ℝ)) / 2) ≤ (-15659179631601 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-15659179631601 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (72304590164289 / 100000000000000 : ℝ)) / 2) ≤ (-32408139546127 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-32408139546127 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (35538448308441 / 50000000000000 : ℝ)) / 2) ≤ (-8522029129607 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-8522029129607 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (69302525677587 / 100000000000000 : ℝ)) / 2) ≤ (-1827068376041 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-1827068376041 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (33427981376059 / 50000000000000 : ℝ)) / 2) ≤ (-39974103991111 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-39974103991111 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (15904817256397 / 25000000000000 : ℝ)) / 2) ≤ (-11151978752993 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-11151978752993 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (59494310201249 / 100000000000000 : ℝ)) / 2) ≤ (-25336697978029 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-25336697978029 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (54413656510711 / 100000000000000 : ℝ)) / 2) ≤ (-58406175703229 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-58406175703229 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (120870729939 / 250000000000 : ℝ)) / 2) ≤ (-68047154937307 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-68047154937307 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (10327412453101 / 25000000000000 : ℝ)) / 2) ≤ (-79850783353097 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-79850783353097 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (33341210069291 / 100000000000000 : ℝ)) / 2) ≤ (-1470507707433 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-1470507707433 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (24482242341347 / 100000000000000 : ℝ)) / 2) ≤ (-11126175578227 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-11126175578227 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((11915720012147 / 16000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (14586405357387 / 100000000000000 : ℝ)) / 2) ≤ (-132335862136659 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-132335862136659 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (11915720012147 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_645 : Uρ (746637295669 / 1000000000000 : ℝ) ≤ (-13158393979419221713642131 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (37009160277631 / 50000000000000 : ℝ)) / 2) ≤ (-7521364931751 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-7521364931751 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (36889095663133 / 50000000000000 : ℝ)) / 2) ≤ (-30408751805573 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-30408751805573 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (36648506800997 / 50000000000000 : ℝ)) / 2) ≤ (-6211629498299 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-6211629498299 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (72495146101113 / 100000000000000 : ℝ)) / 2) ≤ (-32145045695591 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-32145045695591 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (71267576266977 / 100000000000000 : ℝ)) / 2) ≤ (-8455121156007 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-8455121156007 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (13898697985559 / 20000000000000 : ℝ)) / 2) ≤ (-18133446672059 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-18133446672059 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (536380329211 / 800000000000 : ℝ)) / 2) ≤ (-9922400293853 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-9922400293853 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (6381210099107 / 10000000000000 : ℝ)) / 2) ≤ (-5538620314071 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-5538620314071 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (29844793719677 / 50000000000000 : ℝ)) / 2) ≤ (-50353756043403 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-50353756043403 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (27306774190139 / 50000000000000 : ℝ)) / 2) ≤ (-14514189726013 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-14514189726013 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (24278368790357 / 50000000000000 : ℝ)) / 2) ≤ (-67654028311841 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-67654028311841 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (41533991760641 / 100000000000000 : ℝ)) / 2) ≤ (-39695464764803 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-39695464764803 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (16798066199843 / 50000000000000 : ℝ)) / 2) ≤ (-2338584100079 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-2338584100079 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (24801890885763 / 100000000000000 : ℝ)) / 2) ≤ (-110488766883183 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-110488766883183 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((746637295669 / 1000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (754201489961 / 5000000000000 : ℝ)) / 2) ≤ (-65525938098321 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-65525938098321 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_646 : Uρ (765809953469387 / 1024000000000000 : ℝ) ≤ (-52358117890121635401232091 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (74140719978019 / 100000000000000 : ℝ)) / 2) ≤ (-748005839757 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-748005839757 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (73900594791161 / 100000000000000 : ℝ)) / 2) ≤ (-15121494174923 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-15121494174923 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (36709714564559 / 50000000000000 : ℝ)) / 2) ≤ (-7722824189649 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-7722824189649 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (72617593713743 / 100000000000000 : ℝ)) / 2) ≤ (-7994087755763 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-7994087755763 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (71390103023239 / 100000000000000 : ℝ)) / 2) ≤ (-16824443403579 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-16824443403579 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (17404049681303 / 25000000000000 : ℝ)) / 2) ≤ (-36090918925131 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-36090918925131 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (8396330336631 / 12500000000000 : ℝ)) / 2) ≤ (-39507213466057 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-39507213466057 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (31968001953699 / 50000000000000 : ℝ)) / 2) ≤ (-2205866868893 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-2205866868893 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (14953763189471 / 25000000000000 : ℝ)) / 2) ≤ (-12537228135611 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-12537228135611 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (54741959884621 / 100000000000000 : ℝ)) / 2) ≤ (-1807278254649 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-1807278254649 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (9738120660359 / 20000000000000 : ℝ)) / 2) ≤ (-67402301601133 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-67402301601133 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (41677972001401 / 100000000000000 : ℝ)) / 2) ≤ (-79096743971817 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-79096743971817 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (16879746107847 / 50000000000000 : ℝ)) / 2) ≤ (-23294980855833 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-23294980855833 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (12502950340729 / 50000000000000 : ℝ)) / 2) ≤ (-4399891269579 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-4399891269579 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (15396551682857 / 100000000000000 : ℝ)) / 2) ≤ (-65124373057387 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-65124373057387 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((765809953469387 / 1024000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (3025367232759 / 100000000000000 : ℝ)) / 2) ≤ (-159760708142751 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (765809953469387 / 1024000000000000 : ℝ) ≤ (-159760708142751 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_647 : Uρ (383531658086859 / 512000000000000 : ℝ) ≤ (-13028015841294940627690393 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (5801806203 / 7812500000 : ℝ)) / 2) ≤ (-29755280001663 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-29755280001663 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (74022998240303 / 100000000000000 : ℝ)) / 2) ≤ (-30077499225331 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-30077499225331 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (73541844600231 / 100000000000000 : ℝ)) / 2) ≤ (-6144944798357 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-6144944798357 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (72740041161737 / 100000000000000 : ℝ)) / 2) ≤ (-31807940563389 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-31807940563389 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (35756314670461 / 50000000000000 : ℝ)) / 2) ≤ (-6695516650107 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-6695516650107 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (69738906432753 / 100000000000000 : ℝ)) / 2) ≤ (-35915254412617 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-35915254412617 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (67293741670627 / 100000000000000 : ℝ)) / 2) ≤ (-39325159703673 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-39325159703673 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (2562396041609 / 4000000000000 : ℝ)) / 2) ≤ (-8785216645921 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-8785216645921 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (59940505395443 / 100000000000000 : ℝ)) / 2) ≤ (-49944498240339 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-49944498240339 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (54870343904683 / 100000000000000 : ℝ)) / 2) ≤ (-3600598364519 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-3600598364519 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (12206102209007 / 25000000000000 : ℝ)) / 2) ≤ (-16787816465433 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-16787816465433 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (1306931711919 / 3125000000000 : ℝ)) / 2) ≤ (-78803572470479 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-78803572470479 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (33922506982681 / 100000000000000 : ℝ)) / 2) ≤ (-46409117711079 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-46409117711079 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (25208853785067 / 100000000000000 : ℝ)) / 2) ≤ (-2737744495693 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-2737744495693 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (3140761788779 / 20000000000000 : ℝ)) / 2) ≤ (-8091351329017 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-8091351329017 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((383531658086859 / 512000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (1070503872903 / 25000000000000 : ℝ)) / 2) ≤ (-2443912401153 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (383531658086859 / 512000000000000 : ℝ) ≤ (-2443912401153 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_648 : Uρ (768316678878049 / 1024000000000000 : ℝ) ≤ (-1620992355279273346368857 / 3125000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (37192759408207 / 50000000000000 : ℝ)) / 2) ≤ (-7397649515867 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-7397649515867 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (7414540167377 / 10000000000000 : ℝ)) / 2) ≤ (-14956141762741 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-14956141762741 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (18416065003903 / 25000000000000 : ℝ)) / 2) ≤ (-30558428266317 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-30558428266317 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (72862488445923 / 100000000000000 : ℝ)) / 2) ≤ (-6327962672033 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-6327962672033 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (35817577611139 / 50000000000000 : ℝ)) / 2) ≤ (-33306572945629 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-33306572945629 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (436635081601 / 625000000000 : ℝ)) / 2) ≤ (-17869949357109 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-17869949357109 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (67416838098159 / 100000000000000 : ℝ)) / 2) ≤ (-39143438660697 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-39143438660697 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (64183792423043 / 100000000000000 : ℝ)) / 2) ≤ (-5466899827119 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-5466899827119 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (15016486357871 / 25000000000000 : ℝ)) / 2) ≤ (-24870255649657 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-24870255649657 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (10999740126587 / 20000000000000 : ℝ)) / 2) ≤ (-11477353078409 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-11477353078409 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (9791630935379 / 20000000000000 : ℝ)) / 2) ≤ (-33450458501883 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-33450458501883 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (41965521514161 / 100000000000000 : ℝ)) / 2) ≤ (-19627851776247 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-19627851776247 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (2130323853207 / 6250000000000 : ℝ)) / 2) ≤ (-577864247199 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-577864247199 / 625000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (25410775515657 / 100000000000000 : ℝ)) / 2) ≤ (-27256544288719 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-27256544288719 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (16006104768309 / 100000000000000 : ℝ)) / 2) ≤ (-128689627303061 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-128689627303061 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((768316678878049 / 1024000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (5248659765317 / 100000000000000 : ℝ)) / 2) ≤ (-76920865683687 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (768316678878049 / 1024000000000000 : ℝ) ≤ (-76920865683687 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_649 : Uρ (38478502079119 / 51200000000000 : ℝ) ≤ (-51634918102225873037722839 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2980316729283 / 4000000000000 : ℝ)) / 2) ≤ (-14713093441217 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-14713093441217 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (74267805091639 / 100000000000000 : ℝ)) / 2) ≤ (-14873670174119 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-14873670174119 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3689333768777 / 5000000000000 : ℝ)) / 2) ≤ (-6078481732411 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-6078481732411 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (72984935567127 / 100000000000000 : ℝ)) / 2) ≤ (-31471968461761 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-31471968461761 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (35878840334771 / 50000000000000 : ℝ)) / 2) ≤ (-16567927444547 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-16567927444547 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (4374019912571 / 6250000000000 : ℝ)) / 2) ≤ (-35564850743357 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-35564850743357 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (67539931989587 / 100000000000000 : ℝ)) / 2) ≤ (-38962049116363 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-38962049116363 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (12861535617817 / 20000000000000 : ℝ)) / 2) ≤ (-43544682097639 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-43544682097639 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (60191372944793 / 100000000000000 : ℝ)) / 2) ≤ (-24768474946817 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-24768474946817 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (27563515130007 / 50000000000000 : ℝ)) / 2) ≤ (-28582238142427 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-28582238142427 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (49091841312281 / 100000000000000 : ℝ)) / 2) ≤ (-3332562548793 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-3332562548793 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (5263636699067 / 12500000000000 : ℝ)) / 2) ≤ (-39110120027773 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-39110120027773 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (34247521067957 / 100000000000000 : ℝ)) / 2) ≤ (-11512504470053 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-11512504470053 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (12805845133587 / 50000000000000 : ℝ)) / 2) ≤ (-108546392673623 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-108546392673623 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (4075928784079 / 25000000000000 : ℝ)) / 2) ≤ (-15991495915689 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-15991495915689 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((38478502079119 / 51200000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (1516393024541 / 25000000000000 : ℝ)) / 2) ≤ (-151678023247381 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (38478502079119 / 51200000000000 : ℝ) ≤ (-151678023247381 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_650 : Uρ (770823404286711 / 1024000000000000 : ℝ) ≤ (-5140065314440841751066167 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (37315158822697 / 50000000000000 : ℝ)) / 2) ≤ (-3657755696213 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-3657755696213 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (74390208493989 / 100000000000000 : ℝ)) / 2) ≤ (-29582668795993 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-29582668795993 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (73909090680289 / 100000000000000 : ℝ)) / 2) ≤ (-30226664263439 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-30226664263439 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (9138422815771 / 12500000000000 : ℝ)) / 2) ≤ (-31304404921349 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-31304404921349 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (35940102842467 / 50000000000000 : ℝ)) / 2) ≤ (-32965428082731 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-32965428082731 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (70107023073343 / 100000000000000 : ℝ)) / 2) ≤ (-17695054709597 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-17695054709597 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (2114469479961 / 3125000000000 : ℝ)) / 2) ≤ (-38780989856649 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-38780989856649 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (2013486189729 / 3125000000000 : ℝ)) / 2) ≤ (-4335453223793 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-4335453223793 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (60316788013493 / 100000000000000 : ℝ)) / 2) ≤ (-9866762441899 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-9866762441899 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (55255332974747 / 100000000000000 : ℝ)) / 2) ≤ (-56942703986863 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-56942703986863 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (24612734612279 / 50000000000000 : ℝ)) / 2) ≤ (-13280452752927 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-13280452752927 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (42252532389179 / 100000000000000 : ℝ)) / 2) ≤ (-77930063601369 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-77930063601369 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (34409529977633 / 100000000000000 : ℝ)) / 2) ≤ (-91743484381067 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-91743484381067 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (25811621554263 / 100000000000000 : ℝ)) / 2) ≤ (-108070348138927 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-108070348138927 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (8298446052161 / 50000000000000 : ℝ)) / 2) ≤ (-63593956285319 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-63593956285319 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((770823404286711 / 1024000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (6787036415719 / 100000000000000 : ℝ)) / 2) ≤ (-18721664268359 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (770823404286711 / 1024000000000000 : ℝ) ≤ (-18721664268359 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_651 : Uρ (386038383495521 / 512000000000000 : ℝ) ≤ (-319803047918445705656613 / 625000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (37376358528191 / 50000000000000 : ℝ)) / 2) ≤ (-7274543310197 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-7274543310197 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (14902522376179 / 20000000000000 : ℝ)) / 2) ≤ (-29418267975573 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-29418267975573 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (74031505930133 / 100000000000000 : ℝ)) / 2) ≤ (-939412317483 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-939412317483 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (73229829323859 / 100000000000000 : ℝ)) / 2) ≤ (-15568560898429 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-15568560898429 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (36001365135329 / 50000000000000 : ℝ)) / 2) ≤ (-32795291533449 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-32795291533449 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (14045945295681 / 20000000000000 : ℝ)) / 2) ≤ (-35215673666589 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-35215673666589 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (67786112219393 / 100000000000000 : ℝ)) / 2) ≤ (-1544010386969 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-1544010386969 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (16138858100623 / 25000000000000 : ℝ)) / 2) ≤ (-8632949522509 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-8632949522509 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (1208843814301 / 2000000000000 : ℝ)) / 2) ≤ (-24565548222461 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-24565548222461 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (5538360896417 / 10000000000000 : ℝ)) / 2) ≤ (-56721445993279 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-56721445993279 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (49359038890663 / 100000000000000 : ℝ)) / 2) ≤ (-6615395139421 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-6615395139421 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (21197919628449 / 50000000000000 : ℝ)) / 2) ≤ (-1941021752973 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-1941021752973 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (8642803256711 / 25000000000000 : ℝ)) / 2) ≤ (-45694303060829 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-45694303060829 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (26010592055231 / 100000000000000 : ℝ)) / 2) ≤ (-107597967973461 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-107597967973461 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (4221466648891 / 25000000000000 : ℝ)) / 2) ≤ (-63228397258627 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-63228397258627 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((386038383495521 / 512000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (148817370791 / 2000000000000 : ℝ)) / 2) ≤ (-148052727432809 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (386038383495521 / 512000000000000 : ℝ) ≤ (-148052727432809 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_652 : Uρ (773330129695373 / 1024000000000000 : ℝ) ≤ (-25469065847224218030439453 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (74875116465051 / 100000000000000 : ℝ)) / 2) ≤ (-28934569015537 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-28934569015537 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (74635015252433 / 100000000000000 : ℝ)) / 2) ≤ (-14627068499099 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-14627068499099 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2317310035167 / 3125000000000 : ℝ)) / 2) ≤ (-3736999680451 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-3736999680451 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4584517247563 / 6250000000000 : ℝ)) / 2) ≤ (-30970118150943 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-30970118150943 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (9015656803613 / 12500000000000 : ℝ)) / 2) ≤ (-6525088850647 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-6525088850647 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (14070485764381 / 20000000000000 : ℝ)) / 2) ≤ (-1752077120803 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-1752077120803 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (67909198585153 / 100000000000000 : ℝ)) / 2) ≤ (-7683971473681 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-7683971473681 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (32339650557523 / 50000000000000 : ℝ)) / 2) ≤ (-2685957925287 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-2685957925287 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (1514189528157 / 2500000000000 : ℝ)) / 2) ≤ (-24464400404831 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-24464400404831 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (55511858413553 / 100000000000000 : ℝ)) / 2) ≤ (-56500699818179 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-56500699818179 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (1546642211943 / 3125000000000 : ℝ)) / 2) ≤ (-32953154962859 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-32953154962859 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (4253901552903 / 10000000000000 : ℝ)) / 2) ≤ (-15470530416041 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-15470530416041 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (34732574766313 / 100000000000000 : ℝ)) / 2) ≤ (-3641415282193 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-3641415282193 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (26208623652361 / 100000000000000 : ℝ)) / 2) ≤ (-53564589570629 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-53564589570629 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (858542539319 / 5000000000000 : ℝ)) / 2) ≤ (-125737998121127 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-125737998121127 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((773330129695373 / 1024000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (4021789055313 / 50000000000000 : ℝ)) / 2) ≤ (-36617942513403 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (773330129695373 / 1024000000000000 : ℝ) ≤ (-36617942513403 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_653 : Uρ (96822936549963 / 128000000000000 : ℝ) ≤ (-2028375567638438735952231 / 4000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (18749378967853 / 25000000000000 : ℝ)) / 2) ≤ (-7192808004529 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-7192808004529 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (74757418608679 / 100000000000000 : ℝ)) / 2) ≤ (-14545137489731 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-14545137489731 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (74276336266193 / 100000000000000 : ℝ)) / 2) ≤ (-14865536606943 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-14865536606943 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (36737361219209 / 50000000000000 : ℝ)) / 2) ≤ (-3850424131369 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-3850424131369 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (36123889080923 / 50000000000000 : ℝ)) / 2) ≤ (-32455885259117 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-32455885259117 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (70475130109387 / 100000000000000 : ℝ)) / 2) ≤ (-34867714603743 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-34867714603743 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (17008070617393 / 25000000000000 : ℝ)) / 2) ≤ (-38239781745099 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-38239781745099 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (6480316424121 / 10000000000000 : ℝ)) / 2) ≤ (-21393134202751 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-21393134202751 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (60692959323359 / 100000000000000 : ℝ)) / 2) ≤ (-24363461762541 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-24363461762541 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (27820040753209 / 50000000000000 : ℝ)) / 2) ≤ (-56280462994321 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-56280462994321 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (24813002682701 / 50000000000000 : ℝ)) / 2) ≤ (-8207416932103 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-8207416932103 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (21341031259909 / 50000000000000 : ℝ)) / 2) ≤ (-77065402051083 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-77065402051083 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (34893619653627 / 100000000000000 : ℝ)) / 2) ≤ (-11335474201033 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-11335474201033 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (13202868734889 / 50000000000000 : ℝ)) / 2) ≤ (-106663911028957 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-106663911028957 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (3490408031491 / 20000000000000 : ℝ)) / 2) ≤ (-125030955998651 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-125030955998651 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((96822936549963 / 128000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (8605912845533 / 100000000000000 : ℝ)) / 2) ≤ (-145001443939957 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (96822936549963 / 128000000000000 : ℝ) ≤ (-145001443939957 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_654 : Uρ (155167371020807 / 204800000000000 : ℝ) ≤ (-50482118300246065456819321 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (18779978818869 / 25000000000000 : ℝ)) / 2) ≤ (-14304080688487 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-14304080688487 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (74879821949707 / 100000000000000 : ℝ)) / 2) ≤ (-451979391239 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-451979391239 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (74398751352947 / 100000000000000 : ℝ)) / 2) ≤ (-14783210286369 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-14783210286369 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (36798584378443 / 50000000000000 : ℝ)) / 2) ≤ (-239351137257 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-239351137257 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (36185150735823 / 50000000000000 : ℝ)) / 2) ≤ (-4035826696641 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-4035826696641 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (35298915173179 / 50000000000000 : ℝ)) / 2) ≤ (-34694189171353 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-34694189171353 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (68155363886093 / 100000000000000 : ℝ)) / 2) ≤ (-9515007904191 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-9515007904191 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (12985404362591 / 20000000000000 : ℝ)) / 2) ≤ (-21298785507481 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-21298785507481 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (30409162690913 / 50000000000000 : ℝ)) / 2) ≤ (-24262731412031 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-24262731412031 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (13942069606141 / 25000000000000 : ℝ)) / 2) ≤ (-11212146614589 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-11212146614589 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (49759403101443 / 100000000000000 : ℝ)) / 2) ≤ (-8176628015157 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-8176628015157 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (42824981524767 / 100000000000000 : ℝ)) / 2) ≤ (-76779112689633 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-76779112689633 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (35054352055781 / 100000000000000 : ℝ)) / 2) ≤ (-18066764511081 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-18066764511081 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (6650488477261 / 25000000000000 : ℝ)) / 2) ≤ (-10620209533411 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-10620209533411 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (3545923053147 / 20000000000000 : ℝ)) / 2) ≤ (-124335143399983 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-124335143399983 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((155167371020807 / 204800000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (285479116657 / 3125000000000 : ℝ)) / 2) ≤ (-28724320226549 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (155167371020807 / 204800000000000 : ℝ) ≤ (-28724320226549 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_655 : Uρ (388545108904183 / 512000000000000 : ℝ) ≤ (-25128105543812811403986699 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (37621157338627 / 50000000000000 : ℝ)) / 2) ≤ (-14222678112409 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-14222678112409 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (75002225275593 / 100000000000000 : ℝ)) / 2) ≤ (-5752670860389 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-5752670860389 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (74521166385873 / 100000000000000 : ℝ)) / 2) ≤ (-29402038627039 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-29402038627039 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (18429903729301 / 25000000000000 : ℝ)) / 2) ≤ (-30470774781417 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-30470774781417 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (72492824360449 / 100000000000000 : ℝ)) / 2) ≤ (-1284705128891 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-1284705128891 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (70720529538287 / 100000000000000 : ℝ)) / 2) ≤ (-34520965066147 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-34520965066147 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (68278442848063 / 100000000000000 : ℝ)) / 2) ≤ (-37880605802353 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-37880605802353 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (8131359232751 / 12500000000000 : ℝ)) / 2) ≤ (-10602308310213 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-10602308310213 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (6094367937659 / 10000000000000 : ℝ)) / 2) ≤ (-48324416950901 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-48324416950901 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (13974112337021 / 25000000000000 : ℝ)) / 2) ≤ (-55841507623589 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-55841507623589 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (49892744446273 / 100000000000000 : ℝ)) / 2) ≤ (-8145921511043 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-8145921511043 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (671371465953 / 1562500000000 : ℝ)) / 2) ≤ (-76493776744551 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-76493776744551 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (35214776251649 / 100000000000000 : ℝ)) / 2) ≤ (-17997090201277 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-17997090201277 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (6699323170661 / 25000000000000 : ℝ)) / 2) ≤ (-105743665960043 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-105743665960043 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (18003743282131 / 100000000000000 : ℝ)) / 2) ≤ (-61825036922209 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-61825036922209 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((388545108904183 / 512000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (301164404859 / 3125000000000 : ℝ)) / 2) ≤ (-142317567767557 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (388545108904183 / 512000000000000 : ℝ) ≤ (-142317567767557 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_656 : Uρ (194899235804257 / 256000000000000 : ℝ) ≤ (-79693059371923046646177 / 160000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (37743556737 / 50000000000 : ℝ)) / 2) ≤ (-7030134734851 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-7030134734851 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (75247031882231 / 100000000000000 : ℝ)) / 2) ≤ (-28437498954067 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-28437498954067 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (747659962913 / 1000000000000 : ℝ)) / 2) ≤ (-908565102233 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-908565102233 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (18491126691633 / 25000000000000 : ℝ)) / 2) ≤ (-30139259619737 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-30139259619737 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (18184467220893 / 25000000000000 : ℝ)) / 2) ≤ (-1986282041167 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-1986282041167 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (70965924808697 / 100000000000000 : ℝ)) / 2) ≤ (-1367016666151 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-1367016666151 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (68524593461253 / 100000000000000 : ℝ)) / 2) ≤ (-4690340302917 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-4690340302917 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (32649280758869 / 50000000000000 : ℝ)) / 2) ≤ (-21016815507003 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-21016815507003 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (1223887029431 / 2000000000000 : ℝ)) / 2) ≤ (-23961781360913 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-23961781360913 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (14038178480803 / 25000000000000 : ℝ)) / 2) ≤ (-55404560509447 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-55404560509447 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (50159259761011 / 100000000000000 : ℝ)) / 2) ≤ (-32339015391533 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-32339015391533 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (540662291323 / 1250000000000 : ℝ)) / 2) ≤ (-37962968270989 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-37962968270989 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (7106943342711 / 20000000000000 : ℝ)) / 2) ≤ (-22323359122989 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-22323359122989 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (5437082564953 / 20000000000000 : ℝ)) / 2) ≤ (-6552294514233 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-6552294514233 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (9271133833269 / 50000000000000 : ℝ)) / 2) ≤ (-30577596730801 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-30577596730801 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((194899235804257 / 256000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (10574105781609 / 100000000000000 : ℝ)) / 2) ≤ (-17486884466651 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (194899235804257 / 256000000000000 : ℝ) ≤ (-17486884466651 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_657 : Uρ (78210366862569 / 102400000000000 : ℝ) ≤ (-49364724513564176241161649 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (9466489032717 / 12500000000000 : ℝ)) / 2) ≤ (-868649165863 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-868649165863 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (75491838429181 / 100000000000000 : ℝ)) / 2) ≤ (-28112702014979 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-28112702014979 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (7501082598457 / 10000000000000 : ℝ)) / 2) ≤ (-28747200089603 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-28747200089603 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (74209397992633 / 100000000000000 : ℝ)) / 2) ≤ (-29808840270519 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-29808840270519 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (72982911748091 / 100000000000000 : ℝ)) / 2) ≤ (-15722265441277 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-15722265441277 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (71211315963607 / 100000000000000 : ℝ)) / 2) ≤ (-528610328969 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-528610328969 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (68770734414001 / 100000000000000 : ℝ)) / 2) ≤ (-37166122287863 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-37166122287863 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (32773113728703 / 50000000000000 : ℝ)) / 2) ≤ (-8331890149879 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-8331890149879 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (7680622024399 / 12500000000000 : ℝ)) / 2) ≤ (-1900973880671 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-1900973880671 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (28204438319609 / 50000000000000 : ℝ)) / 2) ≤ (-6871200320879 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-6871200320879 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (50425554857643 / 100000000000000 : ℝ)) / 2) ≤ (-64191281590479 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-64191281590479 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (8707540167271 / 20000000000000 : ℝ)) / 2) ≤ (-37680912593269 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-37680912593269 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (4481684199517 / 12500000000000 : ℝ)) / 2) ≤ (-88607613356119 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-88607613356119 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (27570242968167 / 100000000000000 : ℝ)) / 2) ≤ (-20788512309651 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-20788512309651 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (4767182473717 / 25000000000000 : ℝ)) / 2) ≤ (-121008635436077 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-121008635436077 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((78210366862569 / 102400000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (11439688762129 / 100000000000000 : ℝ)) / 2) ≤ (-68835473833239 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (78210366862569 / 102400000000000 : ℝ) ≤ (-68835473833239 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_658 : Uρ (49038149627147 / 64000000000000 : ℝ) ≤ (-12231381416271381650614621 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1519534220811 / 2000000000000 : ℝ)) / 2) ≤ (-6868513135389 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-6868513135389 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3786832245851 / 5000000000000 : ℝ)) / 2) ≤ (-1389447831553 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-1389447831553 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (18813913866939 / 25000000000000 : ℝ)) / 2) ≤ (-14210691046479 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-14210691046479 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (74454288601657 / 100000000000000 : ℝ)) / 2) ≤ (-7369877377633 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-7369877377633 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (73227952970657 / 100000000000000 : ℝ)) / 2) ≤ (-6221935057121 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-6221935057121 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (35728351522709 / 50000000000000 : ℝ)) / 2) ≤ (-16743945020227 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-16743945020227 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (13803373161933 / 20000000000000 : ℝ)) / 2) ≤ (-4601349522091 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-4601349522091 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (65793871926247 / 100000000000000 : ℝ)) / 2) ≤ (-20643340799227 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-20643340799227 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (7711944265603 / 12500000000000 : ℝ)) / 2) ≤ (-1885070247641 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-1885070247641 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (7083117359689 / 12500000000000 : ℝ)) / 2) ≤ (-2726830749623 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-2726830749623 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (6336454150843 / 12500000000000 : ℝ)) / 2) ≤ (-2548283804051 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-2548283804051 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (21910968000717 / 50000000000000 : ℝ)) / 2) ≤ (-74801387774509 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-74801387774509 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (282586548361 / 781250000000 : ℝ)) / 2) ≤ (-87927849748439 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-87927849748439 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (27951918999093 / 100000000000000 : ℝ)) / 2) ≤ (-20612151029207 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-20612151029207 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (9792051380157 / 50000000000000 : ℝ)) / 2) ≤ (-59870985929963 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-59870985929963 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((49038149627147 / 64000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (382785198523 / 3125000000000 : ℝ)) / 2) ≤ (-2712081956699 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (49038149627147 / 64000000000000 : ℝ) ≤ (-2712081956699 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_659 : Uρ (393558559721507 / 512000000000000 : ℝ) ≤ (-24245139860676967208844121 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2381922181579 / 3125000000000 : ℝ)) / 2) ≤ (-1697023119927 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-1697023119927 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (949768141829 / 1250000000000 : ℝ)) / 2) ≤ (-5493251203009 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-5493251203009 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (755004847429 / 1000000000000 : ℝ)) / 2) ≤ (-14048311180557 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-14048311180557 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (37349589299837 / 50000000000000 : ℝ)) / 2) ≤ (-7287815046939 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-7287815046939 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (73472992567699 / 100000000000000 : ℝ)) / 2) ≤ (-6155187667183 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-6155187667183 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (71702086095947 / 100000000000000 : ℝ)) / 2) ≤ (-3314589547169 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-3314589547169 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (6926298775013 / 10000000000000 : ℝ)) / 2) ≤ (-36456734970243 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-36456734970243 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (16510373791449 / 25000000000000 : ℝ)) / 2) ≤ (-8183062567531 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-8183062567531 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (12389217165661 / 20000000000000 : ℝ)) / 2) ≤ (-2920673548323 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-2920673548323 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (5692090199411 / 10000000000000 : ℝ)) / 2) ≤ (-13526394814289 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-13526394814289 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (25478749101801 / 50000000000000 : ℝ)) / 2) ≤ (-31612721216909 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-31612721216909 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (1102642453169 / 2500000000000 : ℝ)) / 2) ≤ (-1856114267747 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-1856114267747 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (18243780292971 / 50000000000000 : ℝ)) / 2) ≤ (-17450803687307 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-17450803687307 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (3541321049581 / 12500000000000 : ℝ)) / 2) ≤ (-51095430650453 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-51095430650453 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (20089239746363 / 100000000000000 : ℝ)) / 2) ≤ (-118507891268227 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-118507891268227 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((393558559721507 / 512000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (13012899960171 / 100000000000000 : ℝ)) / 2) ≤ (-5346638836683 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (393558559721507 / 512000000000000 : ℝ) ≤ (-5346638836683 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_660 : Uρ (197405961212919 / 256000000000000 : ℝ) ≤ (-48058757364746658548766453 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (15293261714351 / 20000000000000 : ℝ)) / 2) ≤ (-6707929695431 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-6707929695431 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (15245251543529 / 20000000000000 : ℝ)) / 2) ≤ (-27144593445173 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-27144593445173 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3787265690601 / 5000000000000 : ℝ)) / 2) ≤ (-27772914040893 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-27772914040893 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (74944067992673 / 100000000000000 : ℝ)) / 2) ≤ (-28824085220451 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-28824085220451 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (36859015277713 / 50000000000000 : ℝ)) / 2) ≤ (-6088662515391 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-6088662515391 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (71947465156441 / 100000000000000 : ℝ)) / 2) ≤ (-32805069290161 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-32805069290161 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (17377275083959 / 25000000000000 : ℝ)) / 2) ≤ (-18051964823401 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-18051964823401 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (33144548706981 / 50000000000000 : ℝ)) / 2) ≤ (-20272666933283 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-20272666933283 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (62196571864239 / 100000000000000 : ℝ)) / 2) ≤ (-46336395462133 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-46336395462133 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (2287070692809 / 4000000000000 : ℝ)) / 2) ≤ (-26838238551173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-26838238551173 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (51223153170323 / 100000000000000 : ℝ)) / 2) ≤ (-62746295221033 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-62746295221033 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (11097249071057 / 25000000000000 : ℝ)) / 2) ≤ (-3684566083047 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-3684566083047 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (36802949733963 / 100000000000000 : ℝ)) / 2) ≤ (-86585996580861 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-86585996580861 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (14353155464563 / 50000000000000 : ℝ)) / 2) ≤ (-101332473152047 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-101332473152047 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (205848944079 / 1000000000000 : ℝ)) / 2) ≤ (-14663022013859 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-14663022013859 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((197405961212919 / 256000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (13738627510737 / 100000000000000 : ℝ)) / 2) ≤ (-13183576337733 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (197405961212919 / 256000000000000 : ℝ) ≤ (-13183576337733 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_661 : Uρ (396065285130169 / 512000000000000 : ℝ) ≤ (-952615369553781229432851 / 2000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (15342221464863 / 20000000000000 : ℝ)) / 2) ≤ (-6628023134087 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-6628023134087 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1194860375493 / 1562500000000 : ℝ)) / 2) ≤ (-5364792452869 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-5364792452869 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (18997535669277 / 25000000000000 : ℝ)) / 2) ≤ (-5490050069097 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-5490050069097 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (15037791357313 / 20000000000000 : ℝ)) / 2) ≤ (-14248988798119 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-14248988798119 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (36981533474917 / 50000000000000 : ℝ)) / 2) ≤ (-30111790626573 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-30111790626573 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (72192840267587 / 100000000000000 : ℝ)) / 2) ≤ (-8116350880249 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-8116350880249 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (348776018329 / 500000000000 : ℝ)) / 2) ≤ (-35752371281473 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-35752371281473 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (66536678905087 / 100000000000000 : ℝ)) / 2) ≤ (-40176734205963 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-40176734205963 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (6244701278217 / 10000000000000 : ℝ)) / 2) ≤ (-45943599124271 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-45943599124271 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (11486507232569 / 20000000000000 : ℝ)) / 2) ≤ (-26624645266839 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-26624645266839 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (51488601357853 / 100000000000000 : ℝ)) / 2) ≤ (-2490785023909 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-2490785023909 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (44671839300959 / 100000000000000 : ℝ)) / 2) ≤ (-14628317903739 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-14628317903739 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (4639659187823 / 12500000000000 : ℝ)) / 2) ≤ (-85923665523477 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-85923665523477 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (29079259278383 / 100000000000000 : ℝ)) / 2) ≤ (-100485206726437 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-100485206726437 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (10535867946201 / 50000000000000 : ℝ)) / 2) ≤ (-58064425972791 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-58064425972791 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((396065285130169 / 512000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (14432049678453 / 100000000000000 : ℝ)) / 2) ≤ (-3252444016907 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (396065285130169 / 512000000000000 : ℝ) ≤ (-3252444016907 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_662 : Uρ (794637295669 / 1024000000000 : ℝ) ≤ (-23603075737768115877860651 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (76955906068289 / 100000000000000 : ℝ)) / 2) ≤ (-6548371162963 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-6548371162963 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (7671587028859 / 10000000000000 : ℝ)) / 2) ≤ (-13252177939651 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-13252177939651 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2382342854379 / 3125000000000 : ℝ)) / 2) ≤ (-2712862455359 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-2712862455359 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (15086768997437 / 20000000000000 : ℝ)) / 2) ≤ (-14086465185597 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-14086465185597 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (14841620353341 / 20000000000000 : ℝ)) / 2) ≤ (-7445341294003 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-7445341294003 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (72438211469517 / 100000000000000 : ℝ)) / 2) ≤ (-8031722567721 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-8031722567721 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (70001297837643 / 100000000000000 : ℝ)) / 2) ≤ (-4425256380577 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-4425256380577 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (8348029983753 / 12500000000000 : ℝ)) / 2) ≤ (-9952375873991 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-9952375873991 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (1567435228069 / 2500000000000 : ℝ)) / 2) ≤ (-9110474958101 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-9110474958101 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (57688209805289 / 100000000000000 : ℝ)) / 2) ≤ (-13206000453997 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-13206000453997 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (10350769189587 / 20000000000000 : ℝ)) / 2) ≤ (-30897703094147 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-30897703094147 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (11238558941979 / 25000000000000 : ℝ)) / 2) ≤ (-907441554463 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-907441554463 / 1250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (37430558731441 / 100000000000000 : ℝ)) / 2) ≤ (-21316727647441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-21316727647441 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (29449519601113 / 100000000000000 : ℝ)) / 2) ≤ (-3114021848887 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-3114021848887 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (10775180750121 / 50000000000000 : ℝ)) / 2) ≤ (-4599206063073 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-4599206063073 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((794637295669 / 1024000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (7548809202469 / 50000000000000 : ℝ)) / 2) ≤ (-64219873353049 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (794637295669 / 1024000000000 : ℝ) ≤ (-64219873353049 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_663 : Uρ (398572010538831 / 512000000000000 : ℝ) ≤ (-23392383173956301542278211 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (77200704803761 / 100000000000000 : ℝ)) / 2) ≤ (-5175177731921 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-5175177731921 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (38480338244651 / 50000000000000 : ℝ)) / 2) ≤ (-6546441939951 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-6546441939951 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (38239899901511 / 50000000000000 : ℝ)) / 2) ≤ (-6702007502143 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-6702007502143 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (75678732600293 / 100000000000000 : ℝ)) / 2) ≤ (-6962234167241 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-6962234167241 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (14890627004323 / 20000000000000 : ℝ)) / 2) ≤ (-5890405797787 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-5890405797787 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (72683578801823 / 100000000000000 : ℝ)) / 2) ≤ (-7947380431741 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-7947380431741 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (35123691473807 / 50000000000000 : ℝ)) / 2) ≤ (-1402118408021 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-1402118408021 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (67031780536193 / 100000000000000 : ℝ)) / 2) ≤ (-39443631494207 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-39443631494207 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (31473880708987 / 50000000000000 : ℝ)) / 2) ≤ (-22581354826771 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-22581354826771 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (57943789507753 / 100000000000000 : ℝ)) / 2) ≤ (-26200296734097 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-26200296734097 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (52018890055003 / 100000000000000 : ℝ)) / 2) ≤ (-6132361009483 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-6132361009483 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (2827262128009 / 6250000000000 : ℝ)) / 2) ≤ (-18013119348649 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-18013119348649 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (9435707820453 / 25000000000000 : ℝ)) / 2) ≤ (-42307810451061 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-42307810451061 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (14908596017319 / 50000000000000 : ℝ)) / 2) ≤ (-49411303559273 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-49411303559273 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (22021306945781 / 100000000000000 : ℝ)) / 2) ≤ (-56928242864307 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-56928242864307 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((398572010538831 / 512000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (15738867704449 / 100000000000000 : ℝ)) / 2) ≤ (-6342600032563 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (398572010538831 / 512000000000000 : ℝ) ≤ (-6342600032563 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_664 : Uρ (199912686621581 / 256000000000000 : ℝ) ≤ (-23183244951664604685266211 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (7744550353081 / 10000000000000 : ℝ)) / 2) ≤ (-12779649076209 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-12779649076209 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3088219305369 / 4000000000000 : ℝ)) / 2) ≤ (-25868191437837 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-25868191437837 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (15344925613541 / 20000000000000 : ℝ)) / 2) ≤ (-6622115029411 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-6622115029411 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (37961809815787 / 50000000000000 : ℝ)) / 2) ≤ (-2752598967989 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-2752598967989 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (4668635420621 / 6250000000000 : ℝ)) / 2) ≤ (-2912377490047 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-2912377490047 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (72928942303563 / 100000000000000 : ℝ)) / 2) ≤ (-31453290155731 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-31453290155731 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (14098691818123 / 20000000000000 : ℝ)) / 2) ≤ (-4338136263261 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-4338136263261 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (1345586022553 / 2000000000000 : ℝ)) / 2) ≤ (-39079108074063 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-39079108074063 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (7899758773907 / 12500000000000 : ℝ)) / 2) ≤ (-44774591065141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-44774591065141 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (29099638253919 / 50000000000000 : ℝ)) / 2) ≤ (-51979048258321 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-51979048258321 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (6535467091001 / 12500000000000 : ℝ)) / 2) ≤ (-60854210885587 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-60854210885587 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (910354445693 / 2000000000000 : ℝ)) / 2) ≤ (-35756500479063 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-35756500479063 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (38054116083861 / 100000000000000 : ℝ)) / 2) ≤ (-16793937840957 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-16793937840957 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (3772796394217 / 12500000000000 : ℝ)) / 2) ≤ (-98006605306141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-98006605306141 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (22485054813069 / 100000000000000 : ℝ)) / 2) ≤ (-2255128377039 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-2255128377039 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((199912686621581 / 256000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (817932887333 / 5000000000000 : ℝ)) / 2) ≤ (-31331659006099 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (199912686621581 / 256000000000000 : ℝ) ≤ (-31331659006099 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_665 : Uρ (25145756165739 / 32000000000000 : ℝ) ≤ (-45538835037405106307363251 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (77935100959959 / 100000000000000 : ℝ)) / 2) ≤ (-4985821653403 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-4985821653403 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (9711886844851 / 12500000000000 : ℝ)) / 2) ≤ (-25236048620829 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-25236048620829 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (38607142004991 / 50000000000000 : ℝ)) / 2) ≤ (-1615773015077 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-1615773015077 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (19103347992757 / 25000000000000 : ℝ)) / 2) ≤ (-26883208930903 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-26883208930903 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (18797056391823 / 25000000000000 : ℝ)) / 2) ≤ (-28470484711613 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-28470484711613 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (36709828984481 / 50000000000000 : ℝ)) / 2) ≤ (-3848025923459 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-3848025923459 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (70985584848721 / 100000000000000 : ℝ)) / 2) ≤ (-8503244512223 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-8503244512223 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (16943570741549 / 25000000000000 : ℝ)) / 2) ≤ (-7670813408053 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-7670813408053 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (3981159951513 / 6250000000000 : ℝ)) / 2) ≤ (-44002943720369 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-44002943720369 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (58709977241363 / 100000000000000 : ℝ)) / 2) ≤ (-25570739770479 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-25570739770479 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (52812849650759 / 100000000000000 : ℝ)) / 2) ≤ (-7490312457113 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-7490312457113 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (719992502239 / 1562500000000 : ℝ)) / 2) ≤ (-4402748393861 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-4402748393861 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (19336908885917 / 50000000000000 : ℝ)) / 2) ≤ (-82693487887371 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-82693487887371 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (15452801188913 / 50000000000000 : ℝ)) / 2) ≤ (-602522836379 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-602522836379 / 625000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (23392663492027 / 100000000000000 : ℝ)) / 2) ≤ (-6913874438873 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-6913874438873 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((25145756165739 / 32000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (8771440748139 / 50000000000000 : ℝ)) / 2) ≤ (-24487620282423 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (25145756165739 / 32000000000000 : ℝ) ≤ (-24487620282423 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_666 : Uρ (202419412030243 / 256000000000000 : ℝ) ≤ (-44722429766736504371415607 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1960617458909 / 2500000000000 : ℝ)) / 2) ≤ (-607571623443 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-607571623443 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (39092353333247 / 50000000000000 : ℝ)) / 2) ≤ (-12303938449481 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-12303938449481 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (19425984795451 / 25000000000000 : ℝ)) / 2) ≤ (-25220297428271 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-25220297428271 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (38451581024793 / 50000000000000 : ℝ)) / 2) ≤ (-26244534948517 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-26244534948517 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (75678278397777 / 100000000000000 : ℝ)) / 2) ≤ (-5564287736903 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-5564287736903 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (36955179383921 / 50000000000000 : ℝ)) / 2) ≤ (-7529895411369 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-7529895411369 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (7147767584511 / 10000000000000 : ℝ)) / 2) ≤ (-33325647530891 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-33325647530891 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (17067296778283 / 25000000000000 : ℝ)) / 2) ≤ (-294017981487 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-294017981487 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (64198880245139 / 100000000000000 : ℝ)) / 2) ≤ (-10809333662813 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-10809333662813 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (59220321473931 / 100000000000000 : ℝ)) / 2) ≤ (-50311162608773 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-50311162608773 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (53341207863831 / 100000000000000 : ℝ)) / 2) ≤ (-59000069955437 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-59000069955437 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (2914980647877 / 6250000000000 : ℝ)) / 2) ≤ (-69387883866649 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-69387883866649 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (19644923118473 / 50000000000000 : ℝ)) / 2) ≤ (-81437514996441 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-81437514996441 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (15809936704171 / 50000000000000 : ℝ)) / 2) ≤ (-94837556779621 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-94837556779621 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (6069056386213 / 25000000000000 : ℝ)) / 2) ≤ (-108567770615999 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-108567770615999 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((202419412030243 / 256000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (4666229106981 / 25000000000000 : ℝ)) / 2) ≤ (-2394671508877 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (202419412030243 / 256000000000000 : ℝ) ≤ (-2394671508877 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_667 : Uρ (101836387367287 / 128000000000000 : ℝ) ≤ (-21958321118140792012647217 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (4932143482539 / 6250000000000 : ℝ)) / 2) ≤ (-4736103808247 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-4736103808247 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (19668579590333 / 25000000000000 : ℝ)) / 2) ≤ (-23983626689319 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-23983626689319 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (15638718719529 / 20000000000000 : ℝ)) / 2) ≤ (-6148049288347 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-6148049288347 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (77392929910171 / 100000000000000 : ℝ)) / 2) ≤ (-25609915570503 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-25609915570503 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (76168325337333 / 100000000000000 : ℝ)) / 2) ≤ (-27176581979201 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-27176581979201 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (74401044994353 / 100000000000000 : ℝ)) / 2) ≤ (-29459353810779 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-29459353810779 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (17992433198207 / 25000000000000 : ℝ)) / 2) ≤ (-32643032610013 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-32643032610013 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (6876401524593 / 10000000000000 : ℝ)) / 2) ≤ (-36919734822879 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-36919734822879 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (16174759287947 / 25000000000000 : ℝ)) / 2) ≤ (-42477668132537 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-42477668132537 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (59730318343527 / 100000000000000 : ℝ)) / 2) ≤ (-1237199202349 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-1237199202349 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (26934416787171 / 50000000000000 : ℝ)) / 2) ≤ (-58086726012471 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-58086726012471 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (23599145452701 / 50000000000000 : ℝ)) / 2) ≤ (-34172192392077 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-34172192392077 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (4987796450691 / 12500000000000 : ℝ)) / 2) ≤ (-40100513613207 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-40100513613207 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (1616288910229 / 5000000000000 : ℝ)) / 2) ≤ (-18661248546069 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-18661248546069 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (785571146167 / 3125000000000 : ℝ)) / 2) ≤ (-106586122290261 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-106586122290261 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((101836387367287 / 128000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (4933843110847 / 25000000000000 : ℝ)) / 2) ≤ (-58591741746191 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (101836387367287 / 128000000000000 : ℝ) ≤ (-58591741746191 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_668 : Uρ (40985227487781 / 51200000000000 : ℝ) ≤ (-4312093229553078849049769 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2481371657917 / 3125000000000 : ℝ)) / 2) ≤ (-23062022365763 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-23062022365763 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (7916392984727 / 10000000000000 : ℝ)) / 2) ≤ (-23363249331891 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-23363249331891 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (78683247271619 / 100000000000000 : ℝ)) / 2) ≤ (-2396801783767 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-2396801783767 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (77882695594627 / 100000000000000 : ℝ)) / 2) ≤ (-24979299622521 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-24979299622521 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (15331673299787 / 20000000000000 : ℝ)) / 2) ≤ (-26535860812743 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-26535860812743 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (74891716934927 / 100000000000000 : ℝ)) / 2) ≤ (-28803465936239 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-28803465936239 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (36230878192753 / 50000000000000 : ℝ)) / 2) ≤ (-31965068705529 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-31965068705529 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (69258768993869 / 100000000000000 : ℝ)) / 2) ≤ (-18105145643901 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-18105145643901 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (6519903372103 / 10000000000000 : ℝ)) / 2) ≤ (-41723850740971 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-41723850740971 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (30119988336283 / 50000000000000 : ℝ)) / 2) ≤ (-48671770177147 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-48671770177147 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (6799468512199 / 12500000000000 : ℝ)) / 2) ≤ (-57182278525913 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-57182278525913 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (47755376843781 / 100000000000000 : ℝ)) / 2) ≤ (-67313146798693 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-67313146798693 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (20255776387967 / 50000000000000 : ℝ)) / 2) ≤ (-3949166277067 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-3949166277067 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (33023853270821 / 100000000000000 : ℝ)) / 2) ≤ (-91807828873097 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-91807828873097 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (25980958182057 / 100000000000000 : ℝ)) / 2) ≤ (-104670562409507 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-104670562409507 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((40985227487781 / 51200000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (20762228971041 / 100000000000000 : ℝ)) / 2) ≤ (-2295309407147 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (40985227487781 / 51200000000000 : ℝ) ≤ (-2295309407147 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_669 : Uρ (51544875035809 / 64000000000000 : ℝ) ≤ (-42334829685614189681376487 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (79893490355101 / 100000000000000 : ℝ)) / 2) ≤ (-4489465517719 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-4489465517719 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (79653541128161 / 100000000000000 : ℝ)) / 2) ≤ (-22746697066813 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-22746697066813 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (7917290021749 / 10000000000000 : ℝ)) / 2) ≤ (-5836927706293 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-5836927706293 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (12539593463 / 16000000000 : ℝ)) / 2) ≤ (-12176318446659 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-12176318446659 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (38574200996343 / 50000000000000 : ℝ)) / 2) ≤ (-12949611216117 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-12949611216117 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (7538237486853 / 10000000000000 : ℝ)) / 2) ≤ (-879745662961 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-879745662961 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (14590749459603 / 20000000000000 : ℝ)) / 2) ≤ (-15645846280329 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-15645846280329 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (871918124247 / 1250000000000 : ℝ)) / 2) ≤ (-4438237167087 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-4438237167087 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (2627954944543 / 4000000000000 : ℝ)) / 2) ≤ (-20487895640399 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-20487895640399 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (1518732624541 / 2500000000000 : ℝ)) / 2) ≤ (-23931223227561 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-23931223227561 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (5492197190271 / 10000000000000 : ℝ)) / 2) ≤ (-28143272183507 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-28143272183507 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (48311000576897 / 100000000000000 : ℝ)) / 2) ≤ (-13258770711823 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-13258770711823 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (41117538387381 / 100000000000000 : ℝ)) / 2) ≤ (-19445937885141 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-19445937885141 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (33714584964413 / 100000000000000 : ℝ)) / 2) ≤ (-22585149421679 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-22585149421679 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (26806096843027 / 100000000000000 : ℝ)) / 2) ≤ (-51407764324317 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-51407764324317 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((51544875035809 / 64000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (10875830822993 / 50000000000000 : ℝ)) / 2) ≤ (-7028884109511 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (51544875035809 / 64000000000000 : ℝ) ≤ (-7028884109511 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_670 : Uρ (104343112775949 / 128000000000000 : ℝ) ≤ (-40789829337698339350045381 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (80872684867973 / 100000000000000 : ℝ)) / 2) ≤ (-21229158754071 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-21229158754071 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (40316381544871 / 50000000000000 : ℝ)) / 2) ≤ (-10762440571617 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-10762440571617 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (801522039783 / 1000000000000 : ℝ)) / 2) ≤ (-4423704712991 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-4423704712991 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (79351979994153 / 100000000000000 : ℝ)) / 2) ≤ (-180554491549 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-180554491549 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (2441514262601 / 3125000000000 : ℝ)) / 2) ≤ (-24637988011453 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-24637988011453 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (190909124487 / 250000000000 : ℝ)) / 2) ≤ (-26861279525967 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-26861279525967 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (73937633691981 / 100000000000000 : ℝ)) / 2) ≤ (-29958456926949 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-29958456926949 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (70742599534157 / 100000000000000 : ℝ)) / 2) ≤ (-6822394271221 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-6822394271221 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (33349048728607 / 50000000000000 : ℝ)) / 2) ≤ (-19748296041623 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-19748296041623 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (12353400838119 / 20000000000000 : ℝ)) / 2) ≤ (-23131974156587 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-23131974156587 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (13993106314583 / 25000000000000 : ℝ)) / 2) ≤ (-27260256370819 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-27260256370819 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (24709029289343 / 50000000000000 : ℝ)) / 2) ≤ (-6428990020109 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-6428990020109 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (21160235649239 / 50000000000000 : ℝ)) / 2) ≤ (-75436536950013 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-75436536950013 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (7015149796573 / 20000000000000 : ℝ)) / 2) ≤ (-17498704796327 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-17498704796327 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (28409827986177 / 100000000000000 : ℝ)) / 2) ≤ (-1985367830773 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-1985367830773 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((104343112775949 / 128000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (23636883632137 / 100000000000000 : ℝ)) / 2) ≤ (-27036694233167 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (104343112775949 / 128000000000000 : ℝ) ≤ (-27036694233167 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_671 : Uρ (2639911887007 / 3200000000000 : ℝ) ≤ (-19639401911836872200714297 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (40925939631803 / 50000000000000 : ℝ)) / 2) ≤ (-4005130185681 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-4005130185681 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (81611984275061 / 100000000000000 : ℝ)) / 2) ≤ (-39683230509 / 195312500000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-39683230509 / 195312500000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (40565752491803 / 50000000000000 : ℝ)) / 2) ≤ (-163314560441 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-163314560441 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (80331492768039 / 100000000000000 : ℝ)) / 2) ≤ (-1094227316129 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-1094227316129 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (4944280587233 / 6250000000000 : ℝ)) / 2) ≤ (-11696238160261 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-11696238160261 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (77344871864537 / 100000000000000 : ℝ)) / 2) ≤ (-25587175984453 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-25587175984453 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (74921397021893 / 100000000000000 : ℝ)) / 2) ≤ (-28642844791779 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-28642844791779 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (35865737911679 / 50000000000000 : ℝ)) / 2) ≤ (-2046087402123 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-2046087402123 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (33848367904993 / 50000000000000 : ℝ)) / 2) ≤ (-38039382879393 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-38039382879393 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (62783478576813 / 100000000000000 : ℝ)) / 2) ≤ (-44691558121539 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-44691558121539 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (57020342032581 / 100000000000000 : ℝ)) / 2) ≤ (-52787279457261 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-52787279457261 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (1578744889153 / 3125000000000 : ℝ)) / 2) ≤ (-7791280157247 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-7791280157247 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (43512184999243 / 100000000000000 : ℝ)) / 2) ≤ (-73154813099699 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-73154813099699 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (3641237040747 / 10000000000000 : ℝ)) / 2) ≤ (-84753905525729 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-84753905525729 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (3744970479369 / 12500000000000 : ℝ)) / 2) ≤ (-749319849091 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-749319849091 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((2639911887007 / 3200000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (25420215890357 / 100000000000000 : ℝ)) / 2) ≤ (-104154206263309 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2639911887007 / 3200000000000 : ℝ) ≤ (-104154206263309 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_672 : Uρ (106849838184611 / 128000000000000 : ℝ) ≤ (-7559882469674203236717089 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (82831073546157 / 100000000000000 : ℝ)) / 2) ≤ (-18836455403719 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-18836455403719 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (5161950294483 / 6250000000000 : ℝ)) / 2) ≤ (-19125143858791 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-19125143858791 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (82110803331999 / 100000000000000 : ℝ)) / 2) ≤ (-19704573083881 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-19704573083881 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (81310997757291 / 100000000000000 : ℝ)) / 2) ≤ (-1292061358149 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-1292061358149 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (40044250878221 / 50000000000000 : ℝ)) / 2) ≤ (-1385143740787 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-1385143740787 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (78326043064207 / 100000000000000 : ℝ)) / 2) ≤ (-24329134265337 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-24329134265337 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (15181008414529 / 20000000000000 : ℝ)) / 2) ≤ (-13672197116821 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-13672197116821 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (36360044978449 / 50000000000000 : ℝ)) / 2) ≤ (-31381643505419 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-31381643505419 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (8586851775787 / 12500000000000 : ℝ)) / 2) ≤ (-36603507363363 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-36603507363363 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (31899393341899 / 50000000000000 : ℝ)) / 2) ≤ (-43144407511071 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-43144407511071 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (725823244487 / 1250000000000 : ℝ)) / 2) ≤ (-51085575467467 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-51085575467467 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (201627626249 / 390625000000 : ℝ)) / 2) ≤ (-30206384496439 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-30206384496439 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (8938715389779 / 20000000000000 : ℝ)) / 2) ≤ (-35467241161441 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-35467241161441 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (37727057866577 / 100000000000000 : ℝ)) / 2) ≤ (-82112270496457 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-82112270496457 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (31463855397639 / 100000000000000 : ℝ)) / 2) ≤ (-92724354318647 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-92724354318647 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((106849838184611 / 128000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (3390220560167 / 12500000000000 : ℝ)) / 2) ≤ (-3138328404363 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (106849838184611 / 128000000000000 : ℝ) ≤ (-3138328404363 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_673 : Uρ (54051600444471 / 64000000000000 : ℝ) ≤ (-18174836265096459405733843 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (8381026771959 / 10000000000000 : ℝ)) / 2) ≤ (-8830617883499 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-8830617883499 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4178521221303 / 5000000000000 : ℝ)) / 2) ≤ (-2243316407469 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-2243316407469 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (41545049558711 / 50000000000000 : ℝ)) / 2) ≤ (-46297765243 / 250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-46297765243 / 250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (82290495239889 / 100000000000000 : ℝ)) / 2) ≤ (-9737962522023 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-9737962522023 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (8106849423361 / 10000000000000 : ℝ)) / 2) ≤ (-327298207251 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-327298207251 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (79307165281869 / 100000000000000 : ℝ)) / 2) ≤ (-23086753655433 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-23086753655433 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (38444286691859 / 50000000000000 : ℝ)) / 2) ≤ (-13031330667511 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-13031330667511 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (36854226241631 / 50000000000000 : ℝ)) / 2) ≤ (-30044193589407 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-30044193589407 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (34846178351949 / 50000000000000 : ℝ)) / 2) ≤ (-219927116729 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-219927116729 / 625000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (4050811457597 / 6250000000000 : ℝ)) / 2) ≤ (-20810836010401 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-20810836010401 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (59109105150769 / 100000000000000 : ℝ)) / 2) ≤ (-49414207510057 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-49414207510057 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (52708874699577 / 100000000000000 : ℝ)) / 2) ≤ (-14633883245667 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-14633883245667 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (1433295148453 / 3125000000000 : ℝ)) / 2) ≤ (-68771853473909 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-68771853473909 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (2438876771789 / 6250000000000 : ℝ)) / 2) ≤ (-79560467483889 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-79560467483889 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (32928385452621 / 100000000000000 : ℝ)) / 2) ≤ (-89682791897911 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-89682791897911 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((54051600444471 / 64000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (1797253183947 / 6250000000000 : ℝ)) / 2) ≤ (-3028793670589 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (54051600444471 / 64000000000000 : ℝ) ≤ (-3028793670589 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_674 : Uρ (27652481574401 / 32000000000000 : ℝ) ≤ (-33532509924589059581636447 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1340135246157 / 1562500000000 : ℝ)) / 2) ≤ (-15351436584749 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-15351436584749 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1069110772337 / 1250000000000 : ℝ)) / 2) ≤ (-15630179922787 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-15630179922787 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (17009736670699 / 20000000000000 : ℝ)) / 2) ≤ (-8094760629461 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-8094760629461 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (42124734366203 / 50000000000000 : ℝ)) / 2) ≤ (-17123973651773 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-17123973651773 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (41514211176769 / 50000000000000 : ℝ)) / 2) ≤ (-3712023022591 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-3712023022591 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (812692698671 / 1000000000000 : ℝ)) / 2) ≤ (-20647446381863 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-20647446381863 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (78855311809901 / 100000000000000 : ℝ)) / 2) ≤ (-23547657360519 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-23547657360519 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (37842231070391 / 50000000000000 : ℝ)) / 2) ≤ (-27422260119023 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-27422260119023 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (14337184695667 / 20000000000000 : ℝ)) / 2) ≤ (-8104437787717 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-8104437787717 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (66838244518063 / 100000000000000 : ℝ)) / 2) ≤ (-19323175221041 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-19323175221041 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (30594622551679 / 50000000000000 : ℝ)) / 2) ≤ (-46158049382601 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-46158049382601 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (10976096878847 / 20000000000000 : ℝ)) / 2) ≤ (-54894660740181 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-54894660740181 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (9636676396549 / 20000000000000 : ℝ)) / 2) ≤ (-64606650319991 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-64606650319991 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (10390040822143 / 25000000000000 : ℝ)) / 2) ≤ (-74698934478821 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-74698934478821 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (17879039308423 / 50000000000000 : ℝ)) / 2) ≤ (-83978872839569 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-83978872839569 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((27652481574401 / 32000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (31863836149463 / 100000000000000 : ℝ)) / 2) ≤ (-90457970860101 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (27652481574401 / 32000000000000 : ℝ) ≤ (-90457970860101 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_675 : Uρ (56558325853133 / 64000000000000 : ℝ) ≤ (-15407952694866375915154457 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (87727043395213 / 100000000000000 : ℝ)) / 2) ≤ (-2618757413611 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-2618757413611 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (87487296545131 / 100000000000000 : ℝ)) / 2) ≤ (-534650898017 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-534650898017 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (87007258360237 / 100000000000000 : ℝ)) / 2) ≤ (-173912227421 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-173912227421 / 1250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (10776051902643 / 12500000000000 : ℝ)) / 2) ≤ (-14826085924059 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-14826085924059 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (10623534882891 / 12500000000000 : ℝ)) / 2) ≤ (-16228837443411 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-16228837443411 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (83231198974899 / 100000000000000 : ℝ)) / 2) ≤ (-4566583123919 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-4566583123919 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (80821644271023 / 100000000000000 : ℝ)) / 2) ≤ (-21094607808001 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-21094607808001 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (77659578610649 / 100000000000000 : ℝ)) / 2) ≤ (-4973578383507 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-4973578383507 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (73677602874427 / 100000000000000 : ℝ)) / 2) ≤ (-14861565303623 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-14861565303623 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (68859636593979 / 100000000000000 : ℝ)) / 2) ≤ (-35759768588089 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-35759768588089 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (63261612525249 / 100000000000000 : ℝ)) / 2) ≤ (-43010556571421 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-43010556571421 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (28518328146027 / 50000000000000 : ℝ)) / 2) ≤ (-5139460858863 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-5139460858863 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (50470863622603 / 100000000000000 : ℝ)) / 2) ≤ (-30317970638471 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-30317970638471 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (22019571675481 / 50000000000000 : ℝ)) / 2) ≤ (-70122446427923 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-70122446427923 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (38479504968263 / 100000000000000 : ℝ)) / 2) ≤ (-15740334130093 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-15740334130093 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((56558325853133 / 64000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (696094286963 / 2000000000000 : ℝ)) / 2) ≤ (-84581308516927 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (56558325853133 / 64000000000000 : ℝ) ≤ (-84581308516927 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_676 : Uρ (7226461069683 / 8000000000000 : ℝ) ≤ (-7047678759931079854828071 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (44842715334423 / 50000000000000 : ℝ)) / 2) ≤ (-10885984280281 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-10885984280281 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (89445728871537 / 100000000000000 : ℝ)) / 2) ≤ (-223049730527 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-223049730527 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (22241456186799 / 25000000000000 : ℝ)) / 2) ≤ (-292177873947 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-292177873947 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (22041834126513 / 25000000000000 : ℝ)) / 2) ≤ (-12579831442331 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-12579831442331 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (43474034595631 / 50000000000000 : ℝ)) / 2) ≤ (-6975355375121 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-6975355375121 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (42596482364301 / 50000000000000 : ℝ)) / 2) ≤ (-3188139061627 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-3188139061627 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (82787599693969 / 100000000000000 : ℝ)) / 2) ≤ (-584391315597 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-584391315597 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (9954233544083 / 12500000000000 : ℝ)) / 2) ≤ (-22377666844421 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-22377666844421 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (75667543927921 / 100000000000000 : ℝ)) / 2) ≤ (-27100358419231 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-27100358419231 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (70877490586471 / 100000000000000 : ℝ)) / 2) ≤ (-16478318727959 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-16478318727959 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (4082934195303 / 6250000000000 : ℝ)) / 2) ≤ (-39964359203047 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-39964359203047 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (29589538915771 / 50000000000000 : ℝ)) / 2) ≤ (-24012020763821 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-24012020763821 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (26365926632253 / 50000000000000 : ℝ)) / 2) ≤ (-56840276977017 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-56840276977017 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (4646843681449 / 10000000000000 : ℝ)) / 2) ≤ (-65794223469501 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-65794223469501 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (41114169299871 / 100000000000000 : ℝ)) / 2) ≤ (-2305616730529 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-2305616730529 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((7226461069683 / 8000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (9404462790129 / 25000000000000 : ℝ)) / 2) ≤ (-39585894002969 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (7226461069683 / 8000000000000 : ℝ) ≤ (-39585894002969 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_677 : Uρ (30159206983063 / 32000000000000 : ℝ) ≤ (-2898184772562841876951017 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (46801102102899 / 50000000000000 : ℝ)) / 2) ≤ (-1652860202127 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-1652860202127 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (93362586841173 / 100000000000000 : ℝ)) / 2) ≤ (-1373346374789 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-1373346374789 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (92882933842887 / 100000000000000 : ℝ)) / 2) ≤ (-7378738784897 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-7378738784897 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (23021277474569 / 25000000000000 : ℝ)) / 2) ≤ (-4116644205387 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-4116644205387 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (4543373346751 / 5000000000000 : ℝ)) / 2) ≤ (-9544580463101 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-9544580463101 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (22279012331247 / 25000000000000 : ℝ)) / 2) ≤ (-2289179733459 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-2289179733459 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (86718481992413 / 100000000000000 : ℝ)) / 2) ≤ (-7039160630637 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-7039160630637 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (83580201971561 / 100000000000000 : ℝ)) / 2) ≤ (-17577209904437 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-17577209904437 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (39821366051259 / 50000000000000 : ℝ)) / 2) ≤ (-11027751709349 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-11027751709349 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (74903727590431 / 100000000000000 : ℝ)) / 2) ≤ (-27581869219911 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-27581869219911 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (69439025904127 / 100000000000000 : ℝ)) / 2) ≤ (-853751004063 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-853751004063 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (63428234502981 / 100000000000000 : ℝ)) / 2) ≤ (-41632756101797 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-41632756101797 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (28593445016521 / 50000000000000 : ℝ)) / 2) ≤ (-49710614947687 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-49710614947687 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (25603056755587 / 50000000000000 : ℝ)) / 2) ≤ (-5776990214723 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-5776990214723 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (46182157177809 / 100000000000000 : ℝ)) / 2) ≤ (-64800228380517 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-64800228380517 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((30159206983063 / 32000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (21480126810829 / 50000000000000 : ℝ)) / 2) ≤ (-69442475984989 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (30159206983063 / 32000000000000 : ℝ) ≤ (-69442475984989 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_678 : Uρ (15706284843697 / 16000000000000 : ℝ) ≤ (-2308581850592452460843851 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (24379744132731 / 25000000000000 : ℝ)) / 2) ≤ (-251214955939 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-251214955939 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (97279436796879 / 100000000000000 : ℝ)) / 2) ≤ (-2757134624601 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-2757134624601 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2420000364037 / 2500000000000 : ℝ)) / 2) ≤ (-1624178344711 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-1624178344711 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (96002800463899 / 100000000000000 : ℝ)) / 2) ≤ (-4067869433601 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-4067869433601 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (94786646484687 / 100000000000000 : ℝ)) / 2) ≤ (-5324539621681 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-5324539621681 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (93038600853979 / 100000000000000 : ℝ)) / 2) ≤ (-7144759766367 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-7144759766367 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (4532407078081 / 5000000000000 : ℝ)) / 2) ≤ (-9661035494369 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-9661035494369 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (43761939307839 / 50000000000000 : ℝ)) / 2) ≤ (-6499096261159 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-6499096261159 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (10451550679617 / 12500000000000 : ℝ)) / 2) ≤ (-8628127254331 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-8628127254331 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (39459473309889 / 50000000000000 : ℝ)) / 2) ≤ (-22488204994007 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-22488204994007 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (2297805638399 / 3125000000000 : ℝ)) / 2) ≤ (-2866948971067 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-2866948971067 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (845465903813 / 1250000000000 : ℝ)) / 2) ≤ (-17827090382501 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-17827090382501 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (61568778030107 / 100000000000000 : ℝ)) / 2) ≤ (-1347246581761 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-1347246581761 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (87213516719 / 156250000000 : ℝ)) / 2) ≤ (-1576473283259 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-1576473283259 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (5104792218593 / 10000000000000 : ℝ)) / 2) ≤ (-1418479639333 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-1418479639333 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((15706284843697 / 16000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (3001787260629 / 6250000000000 : ℝ)) / 2) ≤ (-30413918576211 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (15706284843697 / 16000000000000 : ℝ) ≤ (-30413918576211 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_679 : Uρ (4239911887007 / 4000000000000 : ℝ) ≤ (-1220227708800417357648523 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (21070503617267 / 20000000000000 : ℝ)) / 2) ≤ (2607165632639 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (2607165632639 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (105113116249999 / 100000000000000 : ℝ)) / 2) ≤ (4987648400187 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (4987648400187 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (104634103615249 / 100000000000000 : ℝ)) / 2) ≤ (1133328390651 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (1133328390651 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (25959492653653 / 25000000000000 : ℝ)) / 2) ≤ (3775908111291 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (3775908111291 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (2565611274829 / 2500000000000 : ℝ)) / 2) ≤ (1307938763611 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (1307938763611 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (25220588356283 / 25000000000000 : ℝ)) / 2) ≤ (938721429051 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (938721429051 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (49252188906109 / 50000000000000 : ℝ)) / 2) ≤ (-21461617413 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-21461617413 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (4770228936111 / 5000000000000 : ℝ)) / 2) ≤ (-2214191304903 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-2214191304903 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (22884519134023 / 25000000000000 : ℝ)) / 2) ≤ (-2076346046179 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-2076346046179 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (5432652139719 / 6250000000000 : ℝ)) / 2) ≤ (-1629271321331 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-1629271321331 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (81660119845999 / 100000000000000 : ℝ)) / 2) ≤ (-18565507236083 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-18565507236083 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (37980804134623 / 50000000000000 : ℝ)) / 2) ≤ (-12366531609891 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-12366531609891 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (70167716805107 / 100000000000000 : ℝ)) / 2) ≤ (-31205137786613 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-31205137786613 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (32382129890169 / 50000000000000 : ℝ)) / 2) ≤ (-9358964105031 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-9358964105031 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (12073332225849 / 20000000000000 : ℝ)) / 2) ≤ (-8530804273541 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-8530804273541 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((4239911887007 / 4000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (28814568139699 / 50000000000000 : ℝ)) / 2) ≤ (-22986239246287 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4239911887007 / 4000000000000 : ℝ) ≤ (-22986239246287 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

end Apery
