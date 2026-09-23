import Apery.Table2.Data

set_option maxHeartbeats 4000000

namespace Apery

lemma U_pt_440 : Uρ (1853008205557 / 4000000000000 : ℝ) ≤ (-116215546693062536606512611 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (45679525128339 / 100000000000000 : ℝ)) / 2) ≤ (-78351226803973 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-78351226803973 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (9087574656281 / 20000000000000 : ℝ)) / 2) ≤ (-78877283234241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-78877283234241 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (22476063547053 / 50000000000000 : ℝ)) / 2) ≤ (-79938909664447 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-79938909664447 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (44137994594103 / 100000000000000 : ℝ)) / 2) ≤ (-10216370403153 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-10216370403153 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (42879719493731 / 100000000000000 : ℝ)) / 2) ≤ (-42266305101799 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-42266305101799 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (4103333971737 / 10000000000000 : ℝ)) / 2) ≤ (-88716070146607 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-88716070146607 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (38425606963419 / 100000000000000 : ℝ)) / 2) ≤ (-47388856964857 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-47388856964857 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (17420116024393 / 50000000000000 : ℝ)) / 2) ≤ (-103423651669623 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-103423651669623 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (7491468650933 / 25000000000000 : ℝ)) / 2) ≤ (-115811510952013 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-115811510952013 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (2899273217171 / 12500000000000 : ℝ)) / 2) ≤ (-134403507988223 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-134403507988223 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((1853008205557 / 4000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (12258366600071 / 100000000000000 : ℝ)) / 2) ≤ (-168638212179329 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-168638212179329 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1853008205557 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_441 : Uρ (185565680531 / 400000000000 : ℝ) ≤ (-116053690269002814487821633 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((185565680531 / 400000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (45745741146717 / 100000000000000 : ℝ)) / 2) ≤ (-7820637624329 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-7820637624329 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((185565680531 / 400000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (45504095070099 / 100000000000000 : ℝ)) / 2) ≤ (-39365831442977 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-39365831442977 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((185565680531 / 400000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (22509183145099 / 50000000000000 : ℝ)) / 2) ≤ (-39895858474919 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-39895858474919 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((185565680531 / 400000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2762767559843 / 6250000000000 : ℝ)) / 2) ≤ (-16316211526351 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-16316211526351 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((185565680531 / 400000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (10736531426469 / 25000000000000 : ℝ)) / 2) ≤ (-84378309347467 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-84378309347467 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((185565680531 / 400000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (41100034808219 / 100000000000000 : ℝ)) / 2) ≤ (-88554832382903 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-88554832382903 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((185565680531 / 400000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (38492972977467 / 100000000000000 : ℝ)) / 2) ≤ (-18921108967621 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-18921108967621 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((185565680531 / 400000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (17454569410159 / 50000000000000 : ℝ)) / 2) ≤ (-103233786118461 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-103233786118461 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((185565680531 / 400000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (15019223548423 / 50000000000000 : ℝ)) / 2) ≤ (-3612212816033 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-3612212816033 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((185565680531 / 400000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (23276819940939 / 100000000000000 : ℝ)) / 2) ≤ (-134118534432479 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-134118534432479 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((185565680531 / 400000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (1239166888279 / 10000000000000 : ℝ)) / 2) ≤ (-42025242582817 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-42025242582817 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (185565680531 / 400000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_442 : Uρ (1858305405063 / 4000000000000 : ℝ) ≤ (-7243284087588102940861383 / 6250000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (45811957162133 / 100000000000000 : ℝ)) / 2) ≤ (-15612347039849 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-15612347039849 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (9114063367809 / 20000000000000 : ℝ)) / 2) ≤ (-78586254303887 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-78586254303887 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (22542302707593 / 50000000000000 : ℝ)) / 2) ≤ (-79644740652627 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-79644740652627 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (691727611051 / 1562500000000 : ℝ)) / 2) ≤ (-81431376659963 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-81431376659963 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (8602506265687 / 20000000000000 : ℝ)) / 2) ≤ (-42112123448251 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-42112123448251 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (41166728349037 / 100000000000000 : ℝ)) / 2) ≤ (-22098464013193 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-22098464013193 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (19280167502071 / 50000000000000 : ℝ)) / 2) ≤ (-47216838392521 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-47216838392521 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (3497803519339 / 10000000000000 : ℝ)) / 2) ≤ (-10304429494337 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-10304429494337 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (940968446469 / 3125000000000 : ℝ)) / 2) ≤ (-23074128346851 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-23074128346851 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (11679674759567 / 50000000000000 : ℝ)) / 2) ≤ (-8364660632679 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-8364660632679 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((1858305405063 / 4000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (12523902448937 / 100000000000000 : ℝ)) / 2) ≤ (-2094618176567 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-2094618176567 / 1250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1858305405063 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_443 : Uρ (116309625301 / 250000000000 : ℝ) ≤ (-28933024424771214376024659 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((116309625301 / 250000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (45878173174601 / 100000000000000 : ℝ)) / 2) ≤ (-38958651533299 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-38958651533299 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((116309625301 / 250000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (45636538588331 / 100000000000000 : ℝ)) / 2) ≤ (-9805132109119 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-9805132109119 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((116309625301 / 250000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (45150844469383 / 100000000000000 : ℝ)) / 2) ≤ (-79497980137121 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-79497980137121 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((116309625301 / 250000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4433685304439 / 10000000000000 : ℝ)) / 2) ≤ (-4064095981849 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-4064095981849 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((116309625301 / 250000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (21539468182067 / 50000000000000 : ℝ)) / 2) ≤ (-42035211056517 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-42035211056517 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((116309625301 / 250000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (2577088771709 / 6250000000000 : ℝ)) / 2) ≤ (-88233140303771 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-88233140303771 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((116309625301 / 250000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (2414230816519 / 6250000000000 : ℝ)) / 2) ≤ (-94262108701949 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-94262108701949 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((116309625301 / 250000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (35046921229327 / 100000000000000 : ℝ)) / 2) ≤ (-25713794153717 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-25713794153717 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((116309625301 / 250000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (30183504385497 / 100000000000000 : ℝ)) / 2) ≤ (-57575501519933 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-57575501519933 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((116309625301 / 250000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (732555486781 / 3125000000000 : ℝ)) / 2) ≤ (-66775803338781 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-66775803338781 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((116309625301 / 250000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (12655100799721 / 100000000000000 : ℝ)) / 2) ≤ (-83521749430831 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-83521749430831 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (116309625301 / 250000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_444 : Uρ (1863602604569 / 4000000000000 : ℝ) ≤ (-115572333403060338461274793 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (11486097296033 / 25000000000000 : ℝ)) / 2) ≤ (-77773079242733 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-77773079242733 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1142569007951 / 2500000000000 : ℝ)) / 2) ≤ (-15659213996149 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-15659213996149 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (452170834531 / 1000000000000 : ℝ)) / 2) ≤ (-3174057390817 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-3174057390817 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (44403138769819 / 100000000000000 : ℝ)) / 2) ≤ (-81132685892959 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-81132685892959 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (43145340815683 / 100000000000000 : ℝ)) / 2) ≤ (-4195841713141 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-4195841713141 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (41300110810613 / 100000000000000 : ℝ)) / 2) ≤ (-88072684287647 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-88072684287647 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (9673761794667 / 25000000000000 : ℝ)) / 2) ≤ (-47045419763009 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-47045419763009 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (35115796988963 / 100000000000000 : ℝ)) / 2) ≤ (-102666429613143 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-102666429613143 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (15127994800743 / 50000000000000 : ℝ)) / 2) ≤ (-5746594563859 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-5746594563859 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (183782025021 / 781250000000 : ℝ)) / 2) ≤ (-33317408957387 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-33317408957387 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((1863602604569 / 4000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (12785295804263 / 100000000000000 : ℝ)) / 2) ≤ (-166522947673907 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-166522947673907 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1863602604569 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_445 : Uρ (933125602161 / 2000000000000 : ℝ) ≤ (-57706619672919614060800461 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2300530259537 / 5000000000000 : ℝ)) / 2) ≤ (-77629063127633 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-77629063127633 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (22884491014129 / 50000000000000 : ℝ)) / 2) ≤ (-19537823254379 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-19537823254379 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (45283322366647 / 100000000000000 : ℝ)) / 2) ≤ (-79205103922423 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-79205103922423 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2779339017781 / 6250000000000 : ℝ)) / 2) ≤ (-80983674761061 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-80983674761061 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1728469787431 / 4000000000000 : ℝ)) / 2) ≤ (-83763482615027 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-83763482615027 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (41366799746269 / 100000000000000 : ℝ)) / 2) ≤ (-87912487160309 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-87912487160309 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (38762397367803 / 100000000000000 : ℝ)) / 2) ≤ (-93919868200169 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-93919868200169 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (35184662532647 / 100000000000000 : ℝ)) / 2) ≤ (-102478052427969 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-102478052427969 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (30328446142061 / 100000000000000 : ℝ)) / 2) ≤ (-28678325929069 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-28678325929069 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (737697545871 / 3125000000000 : ℝ)) / 2) ≤ (-132988649424383 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-132988649424383 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((933125602161 / 2000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (6457258903837 / 50000000000000 : ℝ)) / 2) ≤ (-166007651015789 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-166007651015789 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (933125602161 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_446 : Uρ (467887100957 / 1000000000000 : ℝ) ≤ (-115097012013816049005483359 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (9228607439047 / 20000000000000 : ℝ)) / 2) ≤ (-386708258183 / 500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-386708258183 / 500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (45901425390559 / 100000000000000 : ℝ)) / 2) ≤ (-77862366452217 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-77862366452217 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (45415799984457 / 100000000000000 : ℝ)) / 2) ≤ (-39456541637929 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-39456541637929 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (22300997342677 / 50000000000000 : ℝ)) / 2) ≤ (-80686317681177 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-80686317681177 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (43344550692277 / 100000000000000 : ℝ)) / 2) ≤ (-8345748502027 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-8345748502027 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (20750086532099 / 50000000000000 : ℝ)) / 2) ≤ (-87592866216287 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-87592866216287 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (1944854302597 / 5000000000000 : ℝ)) / 2) ≤ (-93578814898797 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-93578814898797 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (35322363211161 / 100000000000000 : ℝ)) / 2) ≤ (-51051200756899 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-51051200756899 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (15236637007537 / 50000000000000 : ℝ)) / 2) ≤ (-114277690392433 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-114277690392433 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (4754093224539 / 20000000000000 : ℝ)) / 2) ≤ (-33107399468723 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-33107399468723 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((467887100957 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (6585078578909 / 50000000000000 : ℝ)) / 2) ≤ (-164992256914499 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-164992256914499 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (467887100957 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_447 : Uρ (938422801667 / 2000000000000 : ℝ) ≤ (-2869583021118950878138561 / 2500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (46275469188187 / 100000000000000 : ℝ)) / 2) ≤ (-15411012768977 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-15411012768977 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (9206773735181 / 20000000000000 : ℝ)) / 2) ≤ (-19393568087927 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-19393568087927 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (45548277325251 / 100000000000000 : ℝ)) / 2) ≤ (-19655478302881 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-19655478302881 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (11183641063607 / 25000000000000 : ℝ)) / 2) ≤ (-20097460780499 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-20097460780499 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (8695470880971 / 20000000000000 : ℝ)) / 2) ≤ (-3326096941977 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-3326096941977 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (10408385089893 / 25000000000000 : ℝ)) / 2) ≤ (-8727427080123 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-8727427080123 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (9757939819603 / 25000000000000 : ℝ)) / 2) ≤ (-11654867556773 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-11654867556773 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (17730011869069 / 50000000000000 : ℝ)) / 2) ≤ (-12716026497393 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-12716026497393 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (6123597924119 / 20000000000000 : ℝ)) / 2) ≤ (-28461035418663 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-28461035418663 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (4786843559337 / 20000000000000 : ℝ)) / 2) ≤ (-131874388964753 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-131874388964753 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((938422801667 / 2000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (13422234699251 / 100000000000000 : ℝ)) / 2) ≤ (-163996249611747 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-163996249611747 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (938422801667 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_448 : Uρ (47053570071 / 100000000000 : ℝ) ≤ (-57236039170442310837620061 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((47053570071 / 100000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (9281580233939 / 20000000000000 : ℝ)) / 2) ≤ (-19192323761147 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-19192323761147 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((47053570071 / 100000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (11541577971239 / 25000000000000 : ℝ)) / 2) ≤ (-77287005932241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-77287005932241 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((47053570071 / 100000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (45680754391439 / 100000000000000 : ℝ)) / 2) ≤ (-78331588786991 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-78331588786991 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((47053570071 / 100000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (44867132999089 / 100000000000000 : ℝ)) / 2) ≤ (-80094245855119 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-80094245855119 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((47053570071 / 100000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (8722031168893 / 20000000000000 : ℝ)) / 2) ≤ (-82848292476331 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-82848292476331 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((47053570071 / 100000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (41766901690083 / 100000000000000 : ℝ)) / 2) ≤ (-17391338861911 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-17391338861911 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((47053570071 / 100000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (39166417206671 / 100000000000000 : ℝ)) / 2) ≤ (-92900236611701 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-92900236611701 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((47053570071 / 100000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (556213196553 / 1562500000000 : ℝ)) / 2) ≤ (-101355472078971 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-101355472078971 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((47053570071 / 100000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (7690648635759 / 25000000000000 : ℝ)) / 2) ≤ (-113412636517319 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-113412636517319 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((47053570071 / 100000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (24097584501177 / 100000000000000 : ℝ)) / 2) ≤ (-131322961298567 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-131322961298567 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((47053570071 / 100000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (6835473730569 / 50000000000000 : ℝ)) / 2) ≤ (-163018652801199 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-163018652801199 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (47053570071 / 100000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_449 : Uρ (943720001173 / 2000000000000 : ℝ) ≤ (-3567600110396224013932101 / 3125000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (9308066627971 / 20000000000000 : ℝ)) / 2) ≤ (-76484340568059 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-76484340568059 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (361709023581 / 781250000000 : ℝ)) / 2) ≤ (-38500281225593 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-38500281225593 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (11453307796351 / 25000000000000 : ℝ)) / 2) ≤ (-78042105102799 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-78042105102799 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (1406240653957 / 3125000000000 : ℝ)) / 2) ≤ (-19949880174629 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-19949880174629 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (43742955031811 / 100000000000000 : ℝ)) / 2) ≤ (-5159067882959 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-5159067882959 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (41900257112687 / 100000000000000 : ℝ)) / 2) ≤ (-43320065099861 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-43320065099861 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (39301059993967 / 100000000000000 : ℝ)) / 2) ≤ (-92562695204457 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-92562695204457 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (35735226193427 / 100000000000000 : ℝ)) / 2) ≤ (-20196834042779 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-20196834042779 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (15453545167977 / 50000000000000 : ℝ)) / 2) ≤ (-112983154215047 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-112983154215047 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (1516285875821 / 6250000000000 : ℝ)) / 2) ≤ (-130775255088183 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-130775255088183 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((943720001173 / 2000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (13916475848859 / 100000000000000 : ℝ)) / 2) ≤ (-81029285175301 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-81029285175301 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (943720001173 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_450 : Uρ (473184300463 / 1000000000000 : ℝ) ≤ (-113856621265784395529632851 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (9334553019753 / 20000000000000 : ℝ)) / 2) ≤ (-15240039157487 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-15240039157487 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (46431198076789 / 100000000000000 : ℝ)) / 2) ≤ (-15342987441313 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-15342987441313 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (91891415419 / 200000000000 : ℝ)) / 2) ≤ (-77753457301957 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-77753457301957 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (45132268044233 / 100000000000000 : ℝ)) / 2) ≤ (-79505662515989 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-79505662515989 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (43875751987343 / 100000000000000 : ℝ)) / 2) ≤ (-82242798880709 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-82242798880709 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (42033606683613 / 100000000000000 : ℝ)) / 2) ≤ (-21581142998353 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-21581142998353 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (4929460974423 / 12500000000000 : ℝ)) / 2) ≤ (-23056577038011 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-23056577038011 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (35872769031583 / 100000000000000 : ℝ)) / 2) ≤ (-6288393432983 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-6288393432983 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (31051478522829 / 100000000000000 : ℝ)) / 2) ≤ (-112555674395041 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-112555674395041 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (1526449617763 / 6250000000000 : ℝ)) / 2) ≤ (-130231212093931 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-130231212093931 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((473184300463 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (14158985522339 / 100000000000000 : ℝ)) / 2) ≤ (-32223035468439 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-32223035468439 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (473184300463 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_451 : Uρ (949017200679 / 2000000000000 : ℝ) ≤ (-113552261586718222927587569 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (46805197046519 / 100000000000000 : ℝ)) / 2) ≤ (-15183371222839 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-15183371222839 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (23281820530429 / 50000000000000 : ℝ)) / 2) ≤ (-19107531384147 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-19107531384147 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (9215636793211 / 20000000000000 : ℝ)) / 2) ≤ (-77465640569459 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-77465640569459 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (45264834359033 / 100000000000000 : ℝ)) / 2) ≤ (-79212666216619 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-79212666216619 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (171908385669 / 390625000000 : ℝ)) / 2) ≤ (-20485356291479 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-20485356291479 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (2108347522919 / 5000000000000 : ℝ)) / 2) ≤ (-86010013274701 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-86010013274701 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (989257519097 / 2500000000000 : ℝ)) / 2) ≤ (-918910674593 / 1000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-918910674593 / 1000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (1800513676909 / 5000000000000 : ℝ)) / 2) ≤ (-50122917452527 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-50122917452527 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (31195760597809 / 100000000000000 : ℝ)) / 2) ≤ (-14016272126213 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-14016272126213 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (4917090289867 / 20000000000000 : ℝ)) / 2) ≤ (-32422693892151 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-32422693892151 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((949017200679 / 2000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (14398629010951 / 100000000000000 : ℝ)) / 2) ≤ (-40046928090581 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-40046928090581 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (949017200679 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_452 : Uρ (59479112527 / 125000000000 : ℝ) ≤ (-113250059211103421236204441 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((59479112527 / 125000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (46937628983213 / 100000000000000 : ℝ)) / 2) ≤ (-75634316998711 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-75634316998711 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((59479112527 / 125000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (46696083971207 / 100000000000000 : ℝ)) / 2) ≤ (-15229224563839 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-15229224563839 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((59479112527 / 125000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (4621065995737 / 10000000000000 : ℝ)) / 2) ≤ (-19294662532949 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-19294662532949 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((59479112527 / 125000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (5674674984757 / 12500000000000 : ℝ)) / 2) ≤ (-78920526754251 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-78920526754251 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((59479112527 / 125000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (8828267856707 / 20000000000000 : ℝ)) / 2) ≤ (-81640959463081 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-81640959463081 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((59479112527 / 125000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (42300288491799 / 100000000000000 : ℝ)) / 2) ≤ (-17139289537853 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-17139289537853 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((59479112527 / 125000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (496311238129 / 1250000000000 : ℝ)) / 2) ≤ (-91556965215099 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-91556965215099 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((59479112527 / 125000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (36147740150651 / 100000000000000 : ℝ)) / 2) ≤ (-49939389484439 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-49939389484439 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((59479112527 / 125000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (15669969013221 / 50000000000000 : ℝ)) / 2) ≤ (-11170664232943 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-11170664232943 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((59479112527 / 125000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (12373676917481 / 50000000000000 : ℝ)) / 2) ≤ (-129153890204029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-129153890204029 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((59479112527 / 125000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (3658886777179 / 25000000000000 : ℝ)) / 2) ≤ (-31855094166733 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-31855094166733 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (59479112527 / 125000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_453 : Uρ (190862880037 / 400000000000 : ℝ) ≤ (-112949953061183410715971841 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((190862880037 / 400000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2353503045447 / 5000000000000 : ℝ)) / 2) ≤ (-18838143482453 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-18838143482453 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((190862880037 / 400000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (46828526808463 / 100000000000000 : ℝ)) / 2) ≤ (-15172584894321 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-15172584894321 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((190862880037 / 400000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (46343135685719 / 100000000000000 : ℝ)) / 2) ≤ (-19223120314121 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-19223120314121 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((190862880037 / 400000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (45529964608253 / 100000000000000 : ℝ)) / 2) ≤ (-19657309781739 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-19657309781739 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((190862880037 / 400000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (354193037311 / 800000000000 : ℝ)) / 2) ≤ (-158869914653 / 195312500000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-158869914653 / 195312500000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((190862880037 / 400000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (21216810418997 / 50000000000000 : ℝ)) / 2) ≤ (-85383868943581 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-85383868943581 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((190862880037 / 400000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (19919741401757 / 50000000000000 : ℝ)) / 2) ≤ (-91223993591163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-91223993591163 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((190862880037 / 400000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (36285169299683 / 100000000000000 : ℝ)) / 2) ≤ (-9951311607831 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-9951311607831 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((190862880037 / 400000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (251872097971 / 800000000000 : ℝ)) / 2) ≤ (-55642525467811 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-55642525467811 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((190862880037 / 400000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (24908907966857 / 100000000000000 : ℝ)) / 2) ≤ (-25724100416017 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-25724100416017 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((190862880037 / 400000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (7434935042607 / 50000000000000 : ℝ)) / 2) ≤ (-79188899611321 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-79188899611321 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (190862880037 / 400000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_454 : Uρ (478481499969 / 1000000000000 : ℝ) ≤ (-112651885861845267059075253 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2950155801487 / 6250000000000 : ℝ)) / 2) ≤ (-75071622434353 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-75071622434353 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (46960969573243 / 100000000000000 : ℝ)) / 2) ≤ (-18895131487469 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-18895131487469 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (5809451394169 / 12500000000000 : ℝ)) / 2) ≤ (-76607129251593 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-76607129251593 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (9132505711299 / 20000000000000 : ℝ)) / 2) ≤ (-78338798376521 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-78338798376521 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (4440691789177 / 10000000000000 : ℝ)) / 2) ≤ (-81042730263219 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-81042730263219 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (5320868443801 / 12500000000000 : ℝ)) / 2) ≤ (-85072270804153 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-85072270804153 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (39974052170253 / 100000000000000 : ℝ)) / 2) ≤ (-90892144840889 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-90892144840889 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (36422561409347 / 100000000000000 : ℝ)) / 2) ≤ (-19829767065261 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-19829767065261 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (790699616701 / 2500000000000 : ℝ)) / 2) ≤ (-13858172964237 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-13858172964237 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (12535060288777 / 50000000000000 : ℝ)) / 2) ≤ (-8005659913503 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-8005659913503 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((478481499969 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (15101718741061 / 100000000000000 : ℝ)) / 2) ≤ (-15749408998553 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-15749408998553 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (478481499969 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_455 : Uρ (959611599691 / 2000000000000 : ℝ) ≤ (-112355803786295915367659197 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2366746236393 / 5000000000000 : ℝ)) / 2) ≤ (-14958291615357 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-14958291615357 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (588667653327 / 1250000000000 : ℝ)) / 2) ≤ (-75298922748463 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-75298922748463 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (46608086362491 / 100000000000000 : ℝ)) / 2) ≤ (-15264517893057 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-15264517893057 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (11448772932393 / 25000000000000 : ℝ)) / 2) ≤ (-15609839917589 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-15609839917589 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (44539703986471 / 100000000000000 : ℝ)) / 2) ≤ (-40372477987041 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-40372477987041 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (10675067170453 / 25000000000000 : ℝ)) / 2) ≤ (-42380823548373 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-42380823548373 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (40108607295343 / 100000000000000 : ℝ)) / 2) ≤ (-452807056491 / 500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-452807056491 / 500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (36559916897223 / 100000000000000 : ℝ)) / 2) ≤ (-49392962968727 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-49392962968727 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (15885928337659 / 50000000000000 : ℝ)) / 2) ≤ (-6902976365467 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-6902976365467 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (2523099821347 / 10000000000000 : ℝ)) / 2) ≤ (-63782004262047 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-63782004262047 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((959611599691 / 2000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (15331205331621 / 100000000000000 : ℝ)) / 2) ≤ (-7831188857061 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-7831188857061 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (959611599691 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_456 : Uρ (240565049861 / 500000000000 : ℝ) ≤ (-28015414036021488578122489 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((240565049861 / 500000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (9493471324247 / 20000000000000 : ℝ)) / 2) ≤ (-37256038229369 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-37256038229369 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((240565049861 / 500000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (47225854887817 / 100000000000000 : ℝ)) / 2) ≤ (-75018110399789 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-75018110399789 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((240565049861 / 500000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (23370280657667 / 50000000000000 : ℝ)) / 2) ≤ (-38019428642681 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-38019428642681 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((240565049861 / 500000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (45927654134197 / 100000000000000 : ℝ)) / 2) ≤ (-2430013684029 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-2430013684029 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((240565049861 / 500000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (44672487967 / 100000000000 : ℝ)) / 2) ≤ (-8044806811151 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-8044806811151 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((240565049861 / 500000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (267709901777 / 625000000000 : ℝ)) / 2) ≤ (-2639124740801 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-2639124740801 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((240565049861 / 500000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (40243148321637 / 100000000000000 : ℝ)) / 2) ≤ (-90231785376423 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-90231785376423 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((240565049861 / 500000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (36697236174531 / 100000000000000 : ℝ)) / 2) ≤ (-98424377265811 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-98424377265811 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((240565049861 / 500000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (15957814813089 / 50000000000000 : ℝ)) / 2) ≤ (-22006349362153 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-22006349362153 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((240565049861 / 500000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (25391547241679 / 100000000000000 : ℝ)) / 2) ≤ (-127040801764893 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-127040801764893 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((240565049861 / 500000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (15558434378491 / 100000000000000 : ℝ)) / 2) ≤ (-9735395773633 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-9735395773633 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (240565049861 / 500000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_457 : Uρ (19351147979 / 40000000000 : ℝ) ≤ (-11147897545662492184428811 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((19351147979 / 40000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (47732220376261 / 100000000000000 : ℝ)) / 2) ≤ (-36977822015569 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-36977822015569 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((19351147979 / 40000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (23745369959869 / 50000000000000 : ℝ)) / 2) ≤ (-1861471014441 / 2500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-1861471014441 / 2500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((19351147979 / 40000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (47005510460801 / 100000000000000 : ℝ)) / 2) ≤ (-471711234321 / 625000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-471711234321 / 625000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((19351147979 / 40000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (46192776664551 / 100000000000000 : ℝ)) / 2) ≤ (-77185406480961 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-77185406480961 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((19351147979 / 40000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (44938049660507 / 100000000000000 : ℝ)) / 2) ≤ (-19964232652517 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-19964232652517 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((19351147979 / 40000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (43100199107867 / 100000000000000 : ℝ)) / 2) ≤ (-10479445212183 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-10479445212183 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((19351147979 / 40000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (10128047159921 / 25000000000000 : ℝ)) / 2) ≤ (-44787913219647 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-44787913219647 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((19351147979 / 40000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (18485883855621 / 50000000000000 : ℝ)) / 2) ≤ (-6106582507813 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-6106582507813 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((19351147979 / 40000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (4025360458087 / 12500000000000 : ℝ)) / 2) ≤ (-54602792271413 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-54602792271413 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((19351147979 / 40000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (5142336817023 / 20000000000000 : ℝ)) / 2) ≤ (-126004224076927 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-126004224076927 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((19351147979 / 40000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (16006503468857 / 100000000000000 : ℝ)) / 2) ≤ (-9630506373509 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-9630506373509 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (19351147979 / 40000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_458 : Uρ (121606824807 / 250000000000 : ℝ) ≤ (-110903491273259753038719151 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((121606824807 / 250000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (11999271022393 / 25000000000000 : ℝ)) / 2) ≤ (-73402290692551 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-73402290692551 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((121606824807 / 250000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (47755624673711 / 100000000000000 : ℝ)) / 2) ≤ (-73902681486139 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-73902681486139 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((121606824807 / 250000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (9454091721369 / 20000000000000 : ℝ)) / 2) ≤ (-18727978436953 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-18727978436953 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((121606824807 / 250000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (46457896199729 / 100000000000000 : ℝ)) / 2) ≤ (-76613666009779 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-76613666009779 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((121606824807 / 250000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (11300900780003 / 25000000000000 : ℝ)) / 2) ≤ (-79269276114399 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-79269276114399 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((121606824807 / 250000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (10841698106289 / 25000000000000 : ℝ)) / 2) ≤ (-3328917319843 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-3328917319843 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((121606824807 / 250000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (40781174229423 / 100000000000000 : ℝ)) / 2) ≤ (-88924208882517 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-88924208882517 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((121606824807 / 250000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (37246159186577 / 100000000000000 : ℝ)) / 2) ≤ (-96991581246137 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-96991581246137 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((121606824807 / 250000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (6497951430479 / 20000000000000 : ℝ)) / 2) ≤ (-10838675429623 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-10838675429623 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((121606824807 / 250000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (26030578696451 / 100000000000000 : ℝ)) / 2) ≤ (-31245112159779 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-31245112159779 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((121606824807 / 250000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (16446632722241 / 100000000000000 : ℝ)) / 2) ≤ (-30491160906719 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-30491160906719 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (121606824807 / 250000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_459 : Uρ (489075898981 / 1000000000000 : ℝ) ≤ (-27583721625864756306487941 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (24130973880927 / 50000000000000 : ℝ)) / 2) ≤ (-14570396510579 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-14570396510579 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (9604101830867 / 20000000000000 : ℝ)) / 2) ≤ (-3667479935443 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-3667479935443 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (23767702885089 / 50000000000000 : ℝ)) / 2) ≤ (-74353170539037 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-74353170539037 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (23361506395359 / 50000000000000 : ℝ)) / 2) ≤ (-76045178984967 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-76045178984967 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (5683643561223 / 12500000000000 : ℝ)) / 2) ≤ (-9835632964451 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-9835632964451 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (43633364630389 / 100000000000000 : ℝ)) / 2) ≤ (-82614058707747 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-82614058707747 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (41050106166693 / 100000000000000 : ℝ)) / 2) ≤ (-88276874760623 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-88276874760623 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (18760206836697 / 50000000000000 : ℝ)) / 2) ≤ (-96283079911629 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-96283079911629 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (8194065020391 / 25000000000000 : ℝ)) / 2) ≤ (-107575117734039 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-107575117734039 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (6587069045033 / 25000000000000 : ℝ)) / 2) ≤ (-1549613949757 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-1549613949757 / 1250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((489075898981 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (527482601271 / 3125000000000 : ℝ)) / 2) ≤ (-150866265145423 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-150866265145423 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (489075898981 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_460 : Uρ (245862249367 / 500000000000 : ℝ) ≤ (-109772874178113316635651493 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((245862249367 / 500000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (2426340569689 / 5000000000000 : ℝ)) / 2) ≤ (-14460937255711 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-14460937255711 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((245862249367 / 500000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (48285393366107 / 100000000000000 : ℝ)) / 2) ≤ (-1455991167949 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-1455991167949 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((245862249367 / 500000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (47800351967141 / 100000000000000 : ℝ)) / 2) ≤ (-18449383235489 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-18449383235489 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((245862249367 / 500000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (5873515810919 / 12500000000000 : ℝ)) / 2) ≤ (-7547990855373 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-7547990855373 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((245862249367 / 500000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (22867342955367 / 50000000000000 : ℝ)) / 2) ≤ (-39052126611569 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-39052126611569 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((245862249367 / 500000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (43899916108159 / 100000000000000 : ℝ)) / 2) ≤ (-16401778561307 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-16401778561307 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((245862249367 / 500000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (20659492749557 / 50000000000000 : ℝ)) / 2) ≤ (-87633767296891 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-87633767296891 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((245862249367 / 500000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (37794534153849 / 100000000000000 : ℝ)) / 2) ≤ (-11947467160287 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-11947467160287 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((245862249367 / 500000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (33062402085451 / 100000000000000 : ℝ)) / 2) ≤ (-106770540619689 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-106770540619689 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((245862249367 / 500000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (26664819325657 / 100000000000000 : ℝ)) / 2) ≤ (-122969882955017 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-122969882955017 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((245862249367 / 500000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (17305484158003 / 100000000000000 : ℝ)) / 2) ≤ (-14931666246709 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-14931666246709 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (245862249367 / 500000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_461 : Uρ (494373098487 / 1000000000000 : ℝ) ≤ (-109217193148173112841184197 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (24395837493003 / 50000000000000 : ℝ)) / 2) ≤ (-35880184540131 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-35880184540131 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (4855027731343 / 10000000000000 : ℝ)) / 2) ≤ (-9031565907399 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-9031565907399 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (24032648606857 / 50000000000000 : ℝ)) / 2) ≤ (-36622483306491 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-36622483306491 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (11813309334587 / 25000000000000 : ℝ)) / 2) ≤ (-74917818486499 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-74917818486499 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (46000215520517 / 100000000000000 : ℝ)) / 2) ≤ (-38763402574001 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-38763402574001 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (22083223616873 / 50000000000000 : ℝ)) / 2) ≤ (-16281478022571 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-16281478022571 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (41587813247011 / 100000000000000 : ℝ)) / 2) ≤ (-86994830851731 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-86994830851731 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (7613704704553 / 20000000000000 : ℝ)) / 2) ≤ (-94881476338023 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-94881476338023 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (16674096227373 / 50000000000000 : ℝ)) / 2) ≤ (-52986446324869 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-52986446324869 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (26980248762537 / 100000000000000 : ℝ)) / 2) ≤ (-24396484342863 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-24396484342863 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((494373098487 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (1772524361987 / 10000000000000 : ℝ)) / 2) ≤ (-147804475657227 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-147804475657227 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (494373098487 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_462 : Uρ (1553192807 / 3125000000 : ℝ) ≤ (-54333802283798354885635813 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1553192807 / 3125000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1962261541567 / 4000000000000 : ℝ)) / 2) ≤ (-7121899870131 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-7121899870131 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((1553192807 / 3125000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (48815161000607 / 100000000000000 : ℝ)) / 2) ≤ (-71708472544917 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-71708472544917 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((1553192807 / 3125000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (48330241525527 / 100000000000000 : ℝ)) / 2) ≤ (-72695437775261 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-72695437775261 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((1553192807 / 3125000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (23759172695667 / 50000000000000 : ℝ)) / 2) ≤ (-37179436581473 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-37179436581473 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((1553192807 / 3125000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (46265737453623 / 100000000000000 : ℝ)) / 2) ≤ (-76952680686517 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-76952680686517 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((1553192807 / 3125000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (222164791867 / 500000000000 : ℝ)) / 2) ≤ (-20202376568183 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-20202376568183 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((1553192807 / 3125000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (20928295202151 / 50000000000000 : ℝ)) / 2) ≤ (-43180005446059 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-43180005446059 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((1553192807 / 3125000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (38342384590857 / 100000000000000 : ℝ)) / 2) ≤ (-47094110910409 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-47094110910409 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((1553192807 / 3125000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (16816820076567 / 50000000000000 : ℝ)) / 2) ≤ (-26295511823831 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-26295511823831 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((1553192807 / 3125000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (27294603102443 / 100000000000000 : ℝ)) / 2) ≤ (-121006418763769 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-121006418763769 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((1553192807 / 3125000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (18139157710259 / 100000000000000 : ℝ)) / 2) ≤ (-146327441156819 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-146327441156819 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1553192807 / 3125000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_463 : Uρ (499670297993 / 1000000000000 : ℝ) ≤ (-108123888990806898251249589 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (24660701026959 / 50000000000000 : ℝ)) / 2) ≤ (-17670135851519 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-17670135851519 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (12270011107963 / 25000000000000 : ℝ)) / 2) ≤ (-71167362037227 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-71167362037227 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (48595184917869 / 100000000000000 : ℝ)) / 2) ≤ (-72148913206271 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-72148913206271 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (47783450692881 / 100000000000000 : ℝ)) / 2) ≤ (-36901518779193 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-36901518779193 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (11632812960367 / 25000000000000 : ℝ)) / 2) ≤ (-76381841704493 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-76381841704493 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (8939889976921 / 20000000000000 : ℝ)) / 2) ≤ (-10026899717213 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-10026899717213 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (10531329484839 / 25000000000000 : ℝ)) / 2) ≤ (-3429170158483 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-3429170158483 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (38616120087809 / 100000000000000 : ℝ)) / 2) ≤ (-46749950090067 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-46749950090067 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (33918753831993 / 100000000000000 : ℝ)) / 2) ≤ (-52198940825877 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-52198940825877 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (6901979767449 / 25000000000000 : ℝ)) / 2) ≤ (-24008314818341 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-24008314818341 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((499670297993 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (9273808887191 / 50000000000000 : ℝ)) / 2) ≤ (-2263804955659 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-2263804955659 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (499670297993 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_464 : Uρ (504967497499 / 1000000000000 : ℝ) ≤ (-53526640981295671411255481 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (12462782242643 / 25000000000000 : ℝ)) / 2) ≤ (-69612253663049 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-69612253663049 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (24804905271469 / 50000000000000 : ℝ)) / 2) ≤ (-8761730920311 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-8761730920311 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (49125069003649 / 100000000000000 : ℝ)) / 2) ≤ (-1421294933679 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-1421294933679 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (4831365322283 / 10000000000000 : ℝ)) / 2) ≤ (-72700558306771 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-72700558306771 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (47062258492197 / 100000000000000 : ℝ)) / 2) ≤ (-15049974179577 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-15049974179577 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (45232375409361 / 100000000000000 : ℝ)) / 2) ≤ (-79037136300183 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-79037136300183 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (10665656973341 / 25000000000000 : ℝ)) / 2) ≤ (-42239860290883 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-42239860290883 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (195816124497 / 500000000000 : ℝ)) / 2) ≤ (-23034442387543 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-23034442387543 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (34488012257653 / 100000000000000 : ℝ)) / 2) ≤ (-1285613939373 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-1285613939373 / 1250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (1129262962391 / 4000000000000 : ℝ)) / 2) ≤ (-59072111095969 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-59072111095969 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((504967497499 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (19349552844381 / 100000000000000 : ℝ)) / 2) ≤ (-142087770435923 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-142087770435923 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (504967497499 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_465 : Uρ (102052939401 / 200000000000 : ℝ) ≤ (-26500980463338288775446497 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((102052939401 / 200000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (25190427870369 / 50000000000000 : ℝ)) / 2) ≤ (-17138813999283 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-17138813999283 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((102052939401 / 200000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (2506978783931 / 5000000000000 : ℝ)) / 2) ≤ (-69031735729691 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-69031735729691 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((102052939401 / 200000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (12413737396723 / 25000000000000 : ℝ)) / 2) ≤ (-17498052975483 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-17498052975483 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((102052939401 / 200000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (48843845280699 / 100000000000000 : ℝ)) / 2) ≤ (-71610111953759 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-71610111953759 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((102052939401 / 200000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (47593236465813 / 100000000000000 : ℝ)) / 2) ≤ (-37065300236057 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-37065300236057 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((102052939401 / 200000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (45765226502363 / 100000000000000 : ℝ)) / 2) ≤ (-77872872796249 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-77872872796249 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((102052939401 / 200000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (5399968796923 / 12500000000000 : ℝ)) / 2) ≤ (-83245823543053 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-83245823543053 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((102052939401 / 200000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (39709858283027 / 100000000000000 : ℝ)) / 2) ≤ (-45397264123311 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-45397264123311 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((102052939401 / 200000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (35056031205841 / 100000000000000 : ℝ)) / 2) ≤ (-101325677140653 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-101325677140653 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((102052939401 / 200000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (28851474119581 / 100000000000000 : ℝ)) / 2) ≤ (-116288206530979 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-116288206530979 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((102052939401 / 200000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (20133491299389 / 100000000000000 : ℝ)) / 2) ≤ (-69702165630129 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-69702165630129 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (102052939401 / 200000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_466 : Uρ (515561896511 / 1000000000000 : ℝ) ≤ (-104974548762107470233148909 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (50910582368989 / 100000000000000 : ℝ)) / 2) ≤ (-33754657064663 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-33754657064663 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (50669339869491 / 100000000000000 : ℝ)) / 2) ≤ (-33990393681031 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-33990393681031 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (3136551673659 / 6250000000000 : ℝ)) / 2) ≤ (-17232765468033 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-17232765468033 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (12343506800961 / 25000000000000 : ℝ)) / 2) ≤ (-70531438442661 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-70531438442661 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (48124186711541 / 100000000000000 : ℝ)) / 2) ≤ (-1460474958899 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-1460474958899 / 2000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (46298005733551 / 100000000000000 : ℝ)) / 2) ≤ (-76722085921469 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-76722085921469 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (10934173073087 / 25000000000000 : ℝ)) / 2) ≤ (-82027171180213 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-82027171180213 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (8051207888627 / 20000000000000 : ℝ)) / 2) ≤ (-89469644229319 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-89469644229319 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (8905717492073 / 25000000000000 : ℝ)) / 2) ≤ (-1559792205923 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-1559792205923 / 1562500000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (29467856221741 / 100000000000000 : ℝ)) / 2) ≤ (-114471537800467 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-114471537800467 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((515561896511 / 1000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (10450729101117 / 50000000000000 : ℝ)) / 2) ≤ (-68411194447761 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-68411194447761 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_467 : Uρ (16577867570387 / 32000000000000 : ℝ) ≤ (-20703521318119147200439787 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (51160231974451 / 100000000000000 : ℝ)) / 2) ≤ (-67020149805981 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-67020149805981 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (12729751726569 / 25000000000000 : ℝ)) / 2) ≤ (-6748929987 / 10000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-6748929987 / 10000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (25217273122091 / 50000000000000 : ℝ)) / 2) ≤ (-68434841291297 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-68434841291297 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (310149300049 / 625000000000 : ℝ)) / 2) ≤ (-2801083615053 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-2801083615053 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (4837440367929 / 10000000000000 : ℝ)) / 2) ≤ (-36253168573467 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-36253168573467 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (11637267452231 / 25000000000000 : ℝ)) / 2) ≤ (-76184326155707 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-76184326155707 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (21994840828029 / 50000000000000 : ℝ)) / 2) ≤ (-81458021518543 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-81458021518543 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (10128323058137 / 25000000000000 : ℝ)) / 2) ≤ (-11106433841449 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-11106433841449 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (35889616647329 / 100000000000000 : ℝ)) / 2) ≤ (-99128508367421 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-99128508367421 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (29757187711797 / 100000000000000 : ℝ)) / 2) ≤ (-14203561136091 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-14203561136091 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (21258344259023 / 100000000000000 : ℝ)) / 2) ≤ (-135638088165139 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-135638088165139 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((16577867570387 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (179796695449 / 5000000000000 : ℝ)) / 2) ≤ (-23873826504519 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-23873826504519 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (16577867570387 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_468 : Uρ (8328877226211 / 16000000000000 : ℝ) ≤ (-102639010026893740582757019 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (10281976309963 / 20000000000000 : ℝ)) / 2) ≤ (-66533366686131 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-66533366686131 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (51168673742721 / 100000000000000 : ℝ)) / 2) ≤ (-67000216363731 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-67000216363731 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (5068426499099 / 10000000000000 : ℝ)) / 2) ≤ (-67941071614763 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-67941071614763 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (49873746665551 / 100000000000000 : ℝ)) / 2) ≤ (-34762637685629 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-34762637685629 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (12156153695667 / 25000000000000 : ℝ)) / 2) ≤ (-4499474733569 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-4499474733569 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (46800118717847 / 100000000000000 : ℝ)) / 2) ≤ (-18912364735673 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-18912364735673 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (44242633041937 / 100000000000000 : ℝ)) / 2) ≤ (-80892135485949 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-80892135485949 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (407704504531 / 1000000000000 : ℝ)) / 2) ≤ (-88237209421579 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-88237209421579 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (3615611909709 / 10000000000000 : ℝ)) / 2) ≤ (-98435483296733 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-98435483296733 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (3755725914939 / 12500000000000 : ℝ)) / 2) ≤ (-112793587905663 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-112793587905663 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (21612220918887 / 100000000000000 : ℝ)) / 2) ≤ (-67236711362557 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-67236711362557 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((8328877226211 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (5097659081557 / 100000000000000 : ℝ)) / 2) ≤ (-37049160584263 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-37049160584263 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (8328877226211 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_469 : Uρ (16737641334457 / 32000000000000 : ℝ) ≤ (-101859189396655685586753089 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (12914882773879 / 25000000000000 : ℝ)) / 2) ≤ (-66048941698831 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-66048941698831 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (3213646273859 / 6250000000000 : ℝ)) / 2) ≤ (-33256756719411 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-33256756719411 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (2546699151477 / 5000000000000 : ℝ)) / 2) ≤ (-33724864371921 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-33724864371921 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (2004944128363 / 4000000000000 : ℝ)) / 2) ≤ (-69025968114953 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-69025968114953 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (24437410055871 / 50000000000000 : ℝ)) / 2) ≤ (-35739748126107 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-35739748126107 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (47051152703087 / 100000000000000 : ℝ)) / 2) ≤ (-18779363290199 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-18779363290199 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (44495547097681 / 100000000000000 : ℝ)) / 2) ≤ (-80329475389497 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-80329475389497 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (41027515883049 / 100000000000000 : ℝ)) / 2) ≤ (-43813404847433 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-43813404847433 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (4552797834831 / 12500000000000 : ℝ)) / 2) ≤ (-19549509090129 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-19549509090129 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (15166867682581 / 50000000000000 : ℝ)) / 2) ≤ (-55983329527879 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-55983329527879 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (2196323364659 / 10000000000000 : ℝ)) / 2) ≤ (-133327597671927 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-133327597671927 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((16737641334457 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (195571484049 / 3125000000000 : ℝ)) / 2) ≤ (-180848340616313 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-180848340616313 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (16737641334457 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_470 : Uρ (33555169550949 / 64000000000000 : ℝ) ≤ (-50745297258182312059113269 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (51784355857377 / 100000000000000 : ℝ)) / 2) ≤ (-32903803193317 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-32903803193317 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1288579340703 / 2500000000000 : ℝ)) / 2) ≤ (-66271047473683 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-66271047473683 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (51058841786467 / 100000000000000 : ℝ)) / 2) ≤ (-2688198397063 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-2688198397063 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (3140533168617 / 6250000000000 : ℝ)) / 2) ≤ (-68777247055293 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-68777247055293 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (12249980159639 / 25000000000000 : ℝ)) / 2) ≤ (-14244885753029 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-14244885753029 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (2948541510861 / 6250000000000 : ℝ)) / 2) ≤ (-74852513718641 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-74852513718641 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (11155497581279 / 25000000000000 : ℝ)) / 2) ≤ (-40024671734201 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-40024671734201 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (41156014344929 / 100000000000000 : ℝ)) / 2) ≤ (-87323042385731 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-87323042385731 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (2284714157823 / 6250000000000 : ℝ)) / 2) ≤ (-48702729806567 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-48702729806567 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (30477446179077 / 100000000000000 : ℝ)) / 2) ≤ (-111556131171519 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-111556131171519 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (4427541730271 / 20000000000000 : ℝ)) / 2) ≤ (-13276151640471 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-13276151640471 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((33555169550949 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (6767785600241 / 100000000000000 : ℝ)) / 2) ≤ (-44732942003307 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-44732942003307 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (33555169550949 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_471 : Uρ (4204382054123 / 8000000000000 : ℝ) ≤ (-101132443962004193422752841 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (25954590305991 / 50000000000000 : ℝ)) / 2) ≤ (-65566852106817 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-65566852106817 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (51668006826209 / 100000000000000 : ℝ)) / 2) ≤ (-16507292007749 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-16507292007749 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (255918501851 / 500000000000 : ℝ)) / 2) ≤ (-13392157786727 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-13392157786727 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (50373457669871 / 100000000000000 : ℝ)) / 2) ≤ (-34264571797767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-34264571797767 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (2456250987737 / 5000000000000 : ℝ)) / 2) ≤ (-70970011651597 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-70970011651597 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (5912771500281 / 12500000000000 : ℝ)) / 2) ≤ (-37294139095323 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-37294139095323 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (44748424456249 / 100000000000000 : ℝ)) / 2) ≤ (-39885002096713 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-39885002096713 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (41284490255727 / 100000000000000 : ℝ)) / 2) ≤ (-87020221947719 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-87020221947719 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (36688412592713 / 100000000000000 : ℝ)) / 2) ≤ (-19412923254503 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-19412923254503 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (612419827139 / 2000000000000 : ℝ)) / 2) ≤ (-111147533400853 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-111147533400853 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (22311517611739 / 100000000000000 : ℝ)) / 2) ≤ (-26439974143363 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-26439974143363 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((4204382054123 / 8000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (3621838043337 / 50000000000000 : ℝ)) / 2) ≤ (-177149990233179 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-177149990233179 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4204382054123 / 8000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_472 : Uρ (33714943315019 / 64000000000000 : ℝ) ≤ (-50391501051135338792786361 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6504250669923 / 12500000000000 : ℝ)) / 2) ≤ (-16331669017077 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-16331669017077 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1294820999409 / 2500000000000 : ℝ)) / 2) ≤ (-65787872279799 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-65787872279799 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (10261711756401 / 20000000000000 : ℝ)) / 2) ≤ (-66717212851059 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-66717212851059 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (25249192064453 / 50000000000000 : ℝ)) / 2) ≤ (-68281654673619 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-68281654673619 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (24625058735521 / 50000000000000 : ℝ)) / 2) ≤ (-35358120798049 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-35358120798049 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (47427676217419 / 100000000000000 : ℝ)) / 2) ≤ (-14864948565219 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-14864948565219 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (22437424783983 / 50000000000000 : ℝ)) / 2) ≤ (-79491453035263 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-79491453035263 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (1656517753013 / 4000000000000 : ℝ)) / 2) ≤ (-86718342332321 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-86718342332321 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (9205335376829 / 25000000000000 : ℝ)) / 2) ≤ (-9672500590467 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-9672500590467 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (30764373217333 / 100000000000000 : ℝ)) / 2) ≤ (-55370422750141 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-55370422750141 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (2248467597353 / 10000000000000 : ℝ)) / 2) ≤ (-131642575258203 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-131642575258203 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((33714943315019 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (7692199051997 / 100000000000000 : ℝ)) / 2) ≤ (-21934811977323 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-21934811977323 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (33714943315019 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_473 : Uρ (16897415098527 / 32000000000000 : ℝ) ≤ (-100441001919256727840964297 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (10431766019927 / 20000000000000 : ℝ)) / 2) ≤ (-650870755001 / 1000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-650870755001 / 1000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (1297941826973 / 2500000000000 : ℝ)) / 2) ≤ (-3277357870479 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-3277357870479 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (25716708511567 / 50000000000000 : ℝ)) / 2) ≤ (-66474228786141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-66474228786141 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (50623310078777 / 100000000000000 : ℝ)) / 2) ≤ (-68034777250221 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-68034777250221 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (49375213798103 / 100000000000000 : ℝ)) / 2) ≤ (-70463115308517 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-70463115308517 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (23776588423949 / 50000000000000 : ℝ)) / 2) ≤ (-74061903904329 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-74061903904329 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (11250316434071 / 25000000000000 : ℝ)) / 2) ≤ (-39606842751891 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-39606842751891 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (10385343815243 / 25000000000000 : ℝ)) / 2) ≤ (-86417397550271 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-86417397550271 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (7390842777147 / 20000000000000 : ℝ)) / 2) ≤ (-12048327387491 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-12048327387491 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (1545379701657 / 5000000000000 : ℝ)) / 2) ≤ (-110336047569577 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-110336047569577 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (4531439730679 / 20000000000000 : ℝ)) / 2) ≤ (-131089547399507 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-131089547399507 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((16897415098527 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (507368251647 / 6250000000000 : ℝ)) / 2) ≤ (-173899430318969 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-173899430318969 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (16897415098527 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_474 : Uρ (33874717079089 / 64000000000000 : ℝ) ≤ (-50052742044403034726323263 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (3267728427049 / 6250000000000 : ℝ)) / 2) ≤ (-32424023825529 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-32424023825529 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (52042506134231 / 100000000000000 : ℝ)) / 2) ≤ (-65307020630079 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-65307020630079 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (25779137547413 / 50000000000000 : ℝ)) / 2) ≤ (-66231833867231 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-66231833867231 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (25374117761621 / 50000000000000 : ℝ)) / 2) ≤ (-67788508308529 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-67788508308529 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (9900061749291 / 20000000000000 : ℝ)) / 2) ≤ (-2194082172619 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-2194082172619 / 3125000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (47678673921993 / 100000000000000 : ℝ)) / 2) ≤ (-36899878867211 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-36899878867211 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (45127673036361 / 100000000000000 : ℝ)) / 2) ≤ (-78936697147577 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-78936697147577 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (41669784767327 / 100000000000000 : ℝ)) / 2) ≤ (-17223476334151 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-17223476334151 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (37087030335631 / 100000000000000 : ℝ)) / 2) ≤ (-9604944656117 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-9604944656117 / 10000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (1552532801641 / 5000000000000 : ℝ)) / 2) ≤ (-109933120043629 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-109933120043629 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (5707275015787 / 25000000000000 : ℝ)) / 2) ≤ (-130540707111181 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-130540707111181 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((33874717079089 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (8524176050301 / 100000000000000 : ℝ)) / 2) ≤ (-86199654569599 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-86199654569599 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (33874717079089 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_475 : Uρ (8488650990281 / 16000000000000 : ℝ) ≤ (-99775700861920154147546323 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (13102119889721 / 25000000000000 : ℝ)) / 2) ≤ (-16152397447431 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-16152397447431 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (6520917392829 / 12500000000000 : ℝ)) / 2) ≤ (-65067459171093 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-65067459171093 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (5168313299831 / 10000000000000 : ℝ)) / 2) ≤ (-8248753155441 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-8248753155441 / 12500000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (25436580233013 / 50000000000000 : ℝ)) / 2) ≤ (-13508568970803 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-13508568970803 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (1985016093061 / 4000000000000 : ℝ)) / 2) ≤ (-69958781001753 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-69958781001753 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (746940116683 / 1562500000000 : ℝ)) / 2) ≤ (-36769150327433 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-36769150327433 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (45254071542513 / 100000000000000 : ℝ)) / 2) ≤ (-78660483553511 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-78660483553511 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (41798172546499 / 100000000000000 : ℝ)) / 2) ≤ (-42909144410319 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-42909144410319 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (7443958291147 / 20000000000000 : ℝ)) / 2) ≤ (-3828539164079 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-3828539164079 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (7798390350373 / 25000000000000 : ℝ)) / 2) ≤ (-109532043684563 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-109532043684563 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (11500197066313 / 50000000000000 : ℝ)) / 2) ≤ (-129995976849467 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-129995976849467 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((8488650990281 / 16000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (8913705481483 / 100000000000000 : ℝ)) / 2) ≤ (-85483825728971 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-85483825728971 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (8488650990281 / 16000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_476 : Uρ (34034490843159 / 64000000000000 : ℝ) ≤ (-9945105544537358776283173 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (1641665758687 / 3125000000000 : ℝ)) / 2) ≤ (-3218584960207 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-3218584960207 / 5000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (52292172104459 / 100000000000000 : ℝ)) / 2) ≤ (-32414235141143 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-32414235141143 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (25903995367401 / 50000000000000 : ℝ)) / 2) ≤ (-525990400679 / 800000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-525990400679 / 800000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (25499042455407 / 50000000000000 : ℝ)) / 2) ≤ (-2691911356569 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-2691911356569 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (49750494548633 / 100000000000000 : ℝ)) / 2) ≤ (-34853783263357 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-34853783263357 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (47929657512769 / 100000000000000 : ℝ)) / 2) ≤ (-36638764516629 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-36638764516629 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (2269023066411 / 5000000000000 : ℝ)) / 2) ≤ (-39192520173141 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-39192520173141 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (41926538798087 / 100000000000000 : ℝ)) / 2) ≤ (-85520113183703 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-85520113183703 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (37352497836021 / 100000000000000 : ℝ)) / 2) ≤ (-95378707644797 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-95378707644797 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (15668156141023 / 50000000000000 : ℝ)) / 2) ≤ (-54566399787047 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-54566399787047 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (1158554716563 / 5000000000000 : ℝ)) / 2) ≤ (-32363820362189 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-32363820362189 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((34034490843159 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (371543537527 / 4000000000000 : ℝ)) / 2) ≤ (-6783844748887 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-6783844748887 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (34034490843159 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_477 : Uρ (17057188862597 / 32000000000000 : ℝ) ≤ (-99131062059749066467410981 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (10531625798027 / 20000000000000 : ℝ)) / 2) ≤ (-16033593300413 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-16033593300413 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (10483401004009 / 20000000000000 : ℝ)) / 2) ≤ (-64590051233 / 100000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-64590051233 / 100000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (51932848305507 / 100000000000000 : ℝ)) / 2) ≤ (-65508155581569 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-65508155581569 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (51123008861259 / 100000000000000 : ℝ)) / 2) ≤ (-67053322538553 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-67053322538553 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (24937792711499 / 50000000000000 : ℝ)) / 2) ≤ (-34728491453691 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-34728491453691 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (48055144084591 / 100000000000000 : ℝ)) / 2) ≤ (-36508719632993 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-36508719632993 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (45506842466143 / 100000000000000 : ℝ)) / 2) ≤ (-78110363187981 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-78110363187981 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (2102744185961 / 5000000000000 : ℝ)) / 2) ≤ (-85222848999897 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-85222848999897 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (37485150057863 / 100000000000000 : ℝ)) / 2) ≤ (-47522561609597 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-47522561609597 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (7869727694051 / 25000000000000 : ℝ)) / 2) ≤ (-108735369106121 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-108735369106121 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (4668242737687 / 20000000000000 : ℝ)) / 2) ≤ (-64459274009941 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-64459274009941 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((17057188862597 / 32000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (4825265967437 / 50000000000000 : ℝ)) / 2) ≤ (-84138973521133 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-84138973521133 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (17057188862597 / 32000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_478 : Uρ (34194264607229 / 64000000000000 : ℝ) ≤ (-98815318657038198641029013 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (6597869211923 / 12500000000000 : ℝ)) / 2) ≤ (-31948804554369 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-31948804554369 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (52541837889719 / 100000000000000 : ℝ)) / 2) ≤ (-64352199312063 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-64352199312063 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (25418801617 / 48828125000 : ℝ)) / 2) ≤ (-16317022236039 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-16317022236039 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (25623966160487 / 50000000000000 : ℝ)) / 2) ≤ (-33404728899017 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-33404728899017 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (10000134991947 / 20000000000000 : ℝ)) / 2) ≤ (-69207027002527 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-69207027002527 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (9636125442063 / 20000000000000 : ℝ)) / 2) ≤ (-72758027777931 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-72758027777931 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (11408303757033 / 25000000000000 : ℝ)) / 2) ≤ (-38918223888831 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-38918223888831 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (10545801876149 / 25000000000000 : ℝ)) / 2) ≤ (-84926490564599 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-84926490564599 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (18808874347101 / 50000000000000 : ℝ)) / 2) ≤ (-47356358480039 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-47356358480039 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (15810679472777 / 50000000000000 : ℝ)) / 2) ≤ (-4333589359181 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-4333589359181 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (11755382406363 / 50000000000000 : ℝ)) / 2) ≤ (-32096426463489 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-32096426463489 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((34194264607229 / 64000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (5000470472049 / 50000000000000 : ℝ)) / 2) ≤ (-33401511899461 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-33401511899461 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (34194264607229 / 64000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_479 : Uρ (68468416096493 / 128000000000000 : ℝ) ≤ (-12332366638326371701365347 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (52845366045437 / 100000000000000 : ℝ)) / 2) ≤ (-31889718474039 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-31889718474039 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 + (26302127153721 / 50000000000000 : ℝ)) / 2) ≤ (-4014592823923 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-4014592823923 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 + (26060067176659 / 50000000000000 : ℝ)) / 2) ≤ (-508970870773 / 781250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-508970870773 / 781250000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 + (6413799233491 / 12500000000000 : ℝ)) / 2) ≤ (-66687748256521 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-66687748256521 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 + (25031609614813 / 50000000000000 : ℝ)) / 2) ≤ (-69082283437051 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 1 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-69082283437051 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 + (48243367489293 / 100000000000000 : ℝ)) / 2) ≤ (-726285752791 / 1000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-726285752791 / 1000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 + (22848199057693 / 50000000000000 : ℝ)) / 2) ≤ (-38849887196977 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-38849887196977 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 + (42247361531563 / 100000000000000 : ℝ)) / 2) ≤ (-21194662308731 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-21194662308731 / 25000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 + (37684028094583 / 100000000000000 : ℝ)) / 2) ≤ (-47273476450501 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-47273476450501 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 + (3961565911493 / 12500000000000 : ℝ)) / 2) ≤ (-108142584031817 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-108142584031817 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 + (11797665558573 / 50000000000000 : ℝ)) / 2) ≤ (-25624144494351 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 2 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-25624144494351 / 20000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((68468416096493 / 128000000000000 : ℝ) - ((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 + (5086097029437 / 50000000000000 : ℝ)) / 2) ≤ (-83194398853179 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-83194398853179 / 50000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (68468416096493 / 128000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

end Apery
