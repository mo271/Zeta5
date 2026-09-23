import Apery.Table2.Data

set_option maxHeartbeats 4000000

namespace Apery

lemma U_pt_680 : Uρ (18213010252359 / 16000000000000 : ℝ) ≤ (-1856915886424111917654243 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (113186056229263 / 100000000000000 : ℝ)) / 2) ≤ (1548300699281 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (1548300699281 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (112946773155161 / 100000000000000 : ℝ)) / 2) ≤ (3043870101781 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (3043870101781 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3514628530133 / 3125000000000 : ℝ)) / 2) ≤ (11752879743859 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (11752879743859 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (111672908800303 / 100000000000000 : ℝ)) / 2) ≤ (2762207642009 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (2762207642009 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (55230823607819 / 50000000000000 : ℝ)) / 2) ≤ (1246454417959 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (1246454417959 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (108724630100223 / 100000000000000 : ℝ)) / 2) ≤ (8416685039831 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (8416685039831 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (106357262572327 / 100000000000000 : ℝ)) / 2) ≤ (3138902069429 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (3138902069429 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (51639049973123 / 50000000000000 : ℝ)) / 2) ≤ (3461162480601 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (3461162480601 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (19889829102347 / 20000000000000 : ℝ)) / 2) ≤ (-19519030569 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (-19519030569 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (4744878024087 / 5000000000000 : ℝ)) / 2) ≤ (-2206025195793 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (-2206025195793 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (4486883581823 / 5000000000000 : ℝ)) / 2) ≤ (-1883678097999 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (-1883678097999 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (16838360051911 / 20000000000000 : ℝ)) / 2) ≤ (-3735683504949 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (-3735683504949 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (78606809560449 / 100000000000000 : ℝ)) / 2) ≤ (-20664666400273 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (-20664666400273 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (73457798554793 / 100000000000000 : ℝ)) / 2) ≤ (-26089013579873 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (-26089013579873 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (69318865876437 / 100000000000000 : ℝ)) / 2) ≤ (-6111701629809 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (-6111701629809 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((18213010252359 / 16000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (33384939046903 / 50000000000000 : ℝ)) / 2) ≤ (-6672322732903 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (18213010252359 / 16000000000000 : ℝ) ≤ (-6672322732903 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_681 : Uρ (1946637295669 / 1600000000000 : ℝ) ≤ (168502135005455457605183 / 3125000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (968156732979 / 800000000000 : ℝ)) / 2) ≤ (9539168229527 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (9539168229527 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (60390205949829 / 50000000000000 : ℝ)) / 2) ≤ (18881120578303 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (18881120578303 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (120302058179503 / 100000000000000 : ℝ)) / 2) ≤ (4621527588401 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (4621527588401 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (23901532128791 / 20000000000000 : ℝ)) / 2) ≤ (557137323247 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (557137323247 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (59149178023973 / 50000000000000 : ℝ)) / 2) ≤ (16822991202711 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (16822991202711 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (14570716095551 / 12500000000000 : ℝ)) / 2) ≤ (15373641525527 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (15373641525527 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (22841497437511 / 20000000000000 : ℝ)) / 2) ≤ (1672992233969 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (1672992233969 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (55572983971439 / 50000000000000 : ℝ)) / 2) ≤ (5385490302819 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (5385490302819 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (53674420360659 / 50000000000000 : ℝ)) / 2) ≤ (7482040425133 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (7482040425133 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (102850923046201 / 100000000000000 : ℝ)) / 2) ≤ (1757402555887 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (1757402555887 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (19555103909019 / 20000000000000 : ℝ)) / 2) ≤ (-529180656229 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (-529180656229 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (18470604218757 / 20000000000000 : ℝ)) / 2) ≤ (-378915649863 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (-378915649863 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (86932620523103 / 100000000000000 : ℝ)) / 2) ≤ (-11193361656603 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (-11193361656603 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (81978137123553 / 100000000000000 : ℝ)) / 2) ≤ (-16001051592009 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (-16001051592009 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (39015396098873 / 50000000000000 : ℝ)) / 2) ≤ (-19915919017097 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (-19915919017097 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((1946637295669 / 1600000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (75617748360581 / 100000000000000 : ℝ)) / 2) ≤ (-4469481176951 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1946637295669 / 1600000000000 : ℝ) ≤ (-4469481176951 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_682 : Uρ (2746637295669 / 2000000000000 : ℝ) ≤ (18323011354893284491293279 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (136686656050257 / 100000000000000 : ℝ)) / 2) ≤ (31252180343749 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (31252180343749 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (136447647418181 / 100000000000000 : ℝ)) / 2) ≤ (1243106072111 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (1243106072111 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (13596980054969 / 10000000000000 : ℝ)) / 2) ≤ (30728262772871 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (30728262772871 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (16897091863441 / 12500000000000 : ℝ)) / 2) ≤ (15073522686087 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (15073522686087 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (16746331707499 / 12500000000000 : ℝ)) / 2) ≤ (14629945884761 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (14629945884761 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (33061307548063 / 25000000000000 : ℝ)) / 2) ≤ (27983849253721 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (27983849253721 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (5196075397091 / 4000000000000 : ℝ)) / 2) ≤ (524753665533 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (524753665533 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (63434475317437 / 50000000000000 : ℝ)) / 2) ≤ (11977396431653 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (11977396431653 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (6156143201903 / 5000000000000 : ℝ)) / 2) ≤ (5274666277711 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (5274666277711 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (118709844014411 / 100000000000000 : ℝ)) / 2) ≤ (8840436899141 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (8840436899141 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (28441432330101 / 25000000000000 : ℝ)) / 2) ≤ (13781083488663 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (13781083488663 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (108530672972611 / 100000000000000 : ℝ)) / 2) ≤ (9567204824369 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (9567204824369 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (25838397343907 / 25000000000000 : ℝ)) / 2) ≤ (20745346793 / 390625000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (20745346793 / 390625000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (98677922981997 / 100000000000000 : ℝ)) / 2) ≤ (277445195147 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (277445195147 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (94996774590311 / 100000000000000 : ℝ)) / 2) ≤ (-439222825759 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (-439222825759 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((2746637295669 / 2000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (92767894674713 / 100000000000000 : ℝ)) / 2) ≤ (-368491277579 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2746637295669 / 2000000000000 : ℝ) ≤ (-368491277579 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_683 : Uρ (6746637295669 / 4000000000000 : ℝ) ≤ (39665646947802634623546901 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (10501297985813 / 6250000000000 : ℝ)) / 2) ≤ (1297294940331 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (1297294940331 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (167782005441247 / 100000000000000 : ℝ)) / 2) ≤ (1617184790211 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (1617184790211 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (20913110895679 / 12500000000000 : ℝ)) / 2) ≤ (51466084844391 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (51466084844391 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (166513731460559 / 100000000000000 : ℝ)) / 2) ≤ (6374319157699 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (6374319157699 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (165312255227141 / 100000000000000 : ℝ)) / 2) ≤ (2513816903931 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (2513816903931 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (163597066509061 / 100000000000000 : ℝ)) / 2) ≤ (49246549574167 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (49246549574167 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (40318679412359 / 25000000000000 : ℝ)) / 2) ≤ (47843724149197 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (47843724149197 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (6331265303553 / 4000000000000 : ℝ)) / 2) ≤ (2876319037187 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (2876319037187 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (38651412836161 / 25000000000000 : ℝ)) / 2) ≤ (21879837171393 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (21879837171393 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (150306992998283 / 100000000000000 : ℝ)) / 2) ≤ (41082332825801 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (41082332825801 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (145535407197369 / 100000000000000 : ℝ)) / 2) ≤ (38067853766793 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (38067853766793 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (140539302711679 / 100000000000000 : ℝ)) / 2) ≤ (34862072546151 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (34862072546151 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (4239424799963 / 3125000000000 : ℝ)) / 2) ≤ (15840946374347 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (15840946374347 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (16414505403447 / 12500000000000 : ℝ)) / 2) ≤ (144027201051 / 500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (144027201051 / 500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (127938610962413 / 100000000000000 : ℝ)) / 2) ≤ (2654088865149 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (2654088865149 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((6746637295669 / 4000000000000 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (125913838803397 / 100000000000000 : ℝ)) / 2) ≤ (25170892569169 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (6746637295669 / 4000000000000 : ℝ) ≤ (25170892569169 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_684 : Uρ (2 : ℝ) ≤ (1423430150552660227493191 / 2500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((2 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (99677432814079 / 50000000000000 : ℝ)) / 2) ≤ (13798334035921 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2 : ℝ) ≤ (13798334035921 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((2 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (49779068015317 / 25000000000000 : ℝ)) / 2) ≤ (68872142572747 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2 : ℝ) ≤ (68872142572747 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((2 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (99319826146537 / 50000000000000 : ℝ)) / 2) ≤ (68633157933607 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2 : ℝ) ≤ (68633157933607 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((2 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (39569960048167 / 20000000000000 : ℝ)) / 2) ≤ (8529560590213 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2 : ℝ) ≤ (8529560590213 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((2 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (196651455627059 / 100000000000000 : ℝ)) / 2) ≤ (33816578269731 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2 : ℝ) ≤ (33816578269731 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((2 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (194943189206237 / 100000000000000 : ℝ)) / 2) ≤ (1669248545467 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2 : ℝ) ≤ (1669248545467 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((2 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (48158732972271 / 25000000000000 : ℝ)) / 2) ≤ (65597593569831 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2 : ℝ) ≤ (65597593569831 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((2 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (189668308846083 / 100000000000000 : ℝ)) / 2) ≤ (32040352500507 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2 : ℝ) ≤ (32040352500507 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((2 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (186038229383717 / 100000000000000 : ℝ)) / 2) ≤ (31104395561193 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2 : ℝ) ≤ (31104395561193 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((2 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (181813104060753 / 100000000000000 : ℝ)) / 2) ≤ (15001934411967 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2 : ℝ) ≤ (15001934411967 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((2 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (11071873838231 / 6250000000000 : ℝ)) / 2) ≤ (28775029135513 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2 : ℝ) ≤ (28775029135513 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((2 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (86150060683731 / 50000000000000 : ℝ)) / 2) ≤ (27480755814317 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2 : ℝ) ≤ (27480755814317 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((2 : ℝ) - ((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 + (33520035265181 / 20000000000000 : ℝ)) / 2) ≤ (52420604517611 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2 : ℝ) ≤ (52420604517611 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((2 : ℝ) - ((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 + (163444551819913 / 100000000000000 : ℝ)) / 2) ≤ (50146762170993 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2 : ℝ) ≤ (50146762170993 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((2 : ℝ) - ((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 + (160236814600081 / 100000000000000 : ℝ)) / 2) ≤ (1209343156009 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2 : ℝ) ≤ (1209343156009 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((2 : ℝ) - ((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 + (158323576601203 / 100000000000000 : ℝ)) / 2) ≤ (1182716903391 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 0 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2 : ℝ) ≤ (1182716903391 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

end Apery
