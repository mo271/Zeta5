import Apery.Table2.Data

set_option maxHeartbeats 4000000

namespace Apery

lemma U_pt_0 : Uρ (0 : ℝ) ≤ (-273856567626306362956419919 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (0 : ℝ) + (592724185889 / 100000000000000 : ℝ)) / 2) ≤ (-5085065481403 / 1000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (0 : ℝ) ≤ (-5085065481403 / 1000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (0 : ℝ) + (595585389833 / 100000000000000 : ℝ)) / 2) ≤ (-490745996749737 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (0 : ℝ) ≤ (-490745996749737 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (0 : ℝ) + (300337682107 / 50000000000000 : ℝ)) / 2) ≤ (-462675203918333 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (0 : ℝ) ≤ (-462675203918333 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (0 : ℝ) + (607887635989 / 100000000000000 : ℝ)) / 2) ≤ (-13398884784307 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (0 : ℝ) ≤ (-13398884784307 / 3125000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (0 : ℝ) + (617049123597 / 100000000000000 : ℝ)) / 2) ≤ (-392751399788187 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (0 : ℝ) ≤ (-392751399788187 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (0 : ℝ) + (627907507841 / 100000000000000 : ℝ)) / 2) ≤ (-357166980210669 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (0 : ℝ) ≤ (-357166980210669 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (0 : ℝ) + (320061279971 / 50000000000000 : ℝ)) / 2) ≤ (-323518249606197 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (0 : ℝ) ≤ (-323518249606197 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (0 : ℝ) + (163316960413 / 25000000000000 : ℝ)) / 2) ≤ (-292628398431827 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (0 : ℝ) ≤ (-292628398431827 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (0 : ℝ) + (333423157647 / 50000000000000 : ℝ)) / 2) ≤ (-264913991431053 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (0 : ℝ) ≤ (-264913991431053 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log ((((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 - (0 : ℝ) + (68031901777 / 10000000000000 : ℝ)) / 2) ≤ (-30070558707733 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (0 : ℝ) ≤ (-30070558707733 / 12500000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log ((((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 - (0 : ℝ) + (346570607531 / 50000000000000 : ℝ)) / 2) ≤ (-109823374929203 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (0 : ℝ) ≤ (-109823374929203 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log ((((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 - (0 : ℝ) + (88099780249 / 12500000000000 : ℝ)) / 2) ≤ (-202163649372809 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (0 : ℝ) ≤ (-202163649372809 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log ((((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 - (0 : ℝ) + (714834368387 / 100000000000000 : ℝ)) / 2) ≤ (-18808673080307 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (0 : ℝ) ≤ (-18808673080307 / 10000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log ((((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 - (0 : ℝ) + (722871698091 / 100000000000000 : ℝ)) / 2) ≤ (-177375627511 / 100000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (0 : ℝ) ≤ (-177375627511 / 100000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log ((((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 - (0 : ℝ) + (728619736567 / 100000000000000 : ℝ)) / 2) ≤ (-84995004877901 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (0 : ℝ) ≤ (-84995004877901 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log ((((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 - (0 : ℝ) + (731879345837 / 100000000000000 : ℝ)) / 2) ≤ (-165896090041089 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (0 : ℝ) ≤ (-165896090041089 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_1 : Uρ (7174131 / 200000000000 : ℝ) ≤ (-17149477848555761531110173 / 6250000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (5888189133 / 1000000000000 : ℝ)) / 2) ≤ (-254556866594449 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-254556866594449 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (118051258123 / 20000000000000 : ℝ)) / 2) ≤ (-491350980787587 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-491350980787587 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (29626473231 / 5000000000000 : ℝ)) / 2) ≤ (-57909556829661 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-57909556829661 / 12500000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (595139247691 / 100000000000000 : ℝ)) / 2) ≤ (-214680327452573 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-214680327452573 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (597439425753 / 100000000000000 : ℝ)) / 2) ≤ (-39334211362119 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-39334211362119 / 10000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (23948412601 / 4000000000000 : ℝ)) / 2) ≤ (-357751852802369 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-357751852802369 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (598245212441 / 100000000000000 : ℝ)) / 2) ≤ (-32409757274627 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-32409757274627 / 10000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (595447450151 / 100000000000000 : ℝ)) / 2) ≤ (-293202920965553 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-293202920965553 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (589933454157 / 100000000000000 : ℝ)) / 2) ≤ (-265484827360731 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-265484827360731 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log ((((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (581631931703 / 100000000000000 : ℝ)) / 2) ≤ (-48226593285341 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-48226593285341 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log ((((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (570862873803 / 100000000000000 : ℝ)) / 2) ≤ (-44042864640219 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-44042864640219 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log ((((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (558375714551 / 100000000000000 : ℝ)) / 2) ≤ (-63353623661 / 31250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-63353623661 / 31250000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log ((((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (136331141339 / 25000000000000 : ℝ)) / 2) ≤ (-188656036006129 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-188656036006129 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log ((((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (5331607687 / 1000000000000 : ℝ)) / 2) ≤ (-88973401536621 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-88973401536621 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log ((((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (523432428239 / 100000000000000 : ℝ)) / 2) ≤ (-2132037513849 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-2132037513849 / 1250000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log ((((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 - (7174131 / 200000000000 : ℝ) + (103500883357 / 20000000000000 : ℝ)) / 2) ≤ (-8323515259017 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (7174131 / 200000000000 : ℝ) ≤ (-8323515259017 / 5000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_2 : Uρ (21522393 / 400000000000 : ℝ) ≤ (-274692134568098847503067623 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (117372950717 / 20000000000000 : ℝ)) / 2) ≤ (-509418838072413 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-509418838072413 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (293790914131 / 50000000000000 : ℝ)) / 2) ≤ (-122913881896303 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-122913881896303 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (117684485529 / 20000000000000 : ℝ)) / 2) ≤ (-463580198446141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-463580198446141 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (58866972701 / 10000000000000 : ℝ)) / 2) ≤ (-429663665637563 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-429663665637563 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (18356167033 / 3125000000000 : ℝ)) / 2) ≤ (-393644861504129 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-393644861504129 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (583572440279 / 100000000000000 : ℝ)) / 2) ≤ (-71611050938931 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-71611050938931 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (57617463127 / 10000000000000 : ℝ)) / 2) ≤ (-324403005961471 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-324403005961471 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (564328550269 / 100000000000000 : ℝ)) / 2) ≤ (-73378052680337 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-73378052680337 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (547448505951 / 100000000000000 : ℝ)) / 2) ≤ (-265800206767041 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-265800206767041 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log ((((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (525391495243 / 100000000000000 : ℝ)) / 2) ≤ (-48291398935361 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-48291398935361 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log ((((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (124652995677 / 25000000000000 : ℝ)) / 2) ≤ (-220549727894429 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-220549727894429 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log ((((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (117077572367 / 25000000000000 : ℝ)) / 2) ≤ (-40616195797341 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-40616195797341 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log ((((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (109139785807 / 25000000000000 : ℝ)) / 2) ≤ (-37804272258893 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-37804272258893 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log ((((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (203180038543 / 50000000000000 : ℝ)) / 2) ≤ (-178328600866603 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-178328600866603 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log ((((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (381495151239 / 100000000000000 : ℝ)) / 2) ≤ (-85479697088039 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-85479697088039 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log ((((7174131 / 100000000000 : ℝ) + (746637295669 / 1000000000000 : ℝ)) / 2 - (21522393 / 400000000000 : ℝ) + (182963243533 / 50000000000000 : ℝ)) / 2) ≤ (-33375268755033 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (21522393 / 400000000000 : ℝ) ≤ (-33375268755033 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_3 : Uρ (7174131 / 100000000000 : ℝ) ≤ (-68760456943802754478209389 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (116981912937 / 20000000000000 : ℝ)) / 2) ≤ (-25486248043401 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-25486248043401 / 5000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (584900636617 / 100000000000000 : ℝ)) / 2) ≤ (-245980732745489 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-245980732745489 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (584292027833 / 100000000000000 : ℝ)) / 2) ≤ (-463886075829993 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-463886075829993 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (291066918583 / 50000000000000 : ℝ)) / 2) ≤ (-214985021125327 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-214985021125327 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (577186146779 / 100000000000000 : ℝ)) / 2) ≤ (-98488218621421 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-98488218621421 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (113607390307 / 20000000000000 : ℝ)) / 2) ≤ (-358366737774393 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-358366737774393 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (276615035179 / 50000000000000 : ℝ)) / 2) ≤ (-64944122594503 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-64944122594503 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (531396455507 / 100000000000000 : ℝ)) / 2) ≤ (-36729947518893 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-36729947518893 / 12500000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (250691387229 / 50000000000000 : ℝ)) / 2) ≤ (-266142213061419 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-266142213061419 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log ((((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (462366927981 / 100000000000000 : ℝ)) / 2) ≤ (-241820147180277 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-241820147180277 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log ((((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (82788847421 / 20000000000000 : ℝ)) / 2) ≤ (-110471403625583 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-110471403625583 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log ((((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (356162953383 / 100000000000000 : ℝ)) / 2) ≤ (-203516053282857 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-203516053282857 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log ((((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (57894843643 / 20000000000000 : ℝ)) / 2) ≤ (-189515425753093 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-189515425753093 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log ((((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (53620805627 / 25000000000000 : ℝ)) / 2) ≤ (-44726593890323 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-44726593890323 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log ((((14825913 / 200000000000 : ℝ) + (89520072139 / 125000000000 : ℝ)) / 2 - (7174131 / 100000000000 : ℝ) + (32693680033 / 25000000000000 : ℝ)) / 2) ≤ (-171659626681907 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-171659626681907 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (7174131 / 100000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_4 : Uρ (14825913 / 200000000000 : ℝ) ≤ (-275101278173292200580074647 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (58464913497 / 10000000000000 : ℝ)) / 2) ≤ (-509765801144519 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-509765801144519 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (292271549227 / 50000000000000 : ℝ)) / 2) ≤ (-492002309782363 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-492002309782363 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (583740237647 / 100000000000000 : ℝ)) / 2) ≤ (-463926969478311 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-463926969478311 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (116251679161 / 20000000000000 : ℝ)) / 2) ≤ (-430011098997753 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-430011098997753 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (575813191081 / 100000000000000 : ℝ)) / 2) ≤ (-196997150654857 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-196997150654857 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (282968256159 / 50000000000000 : ℝ)) / 2) ≤ (-89602214915037 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-89602214915037 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (275051516807 / 50000000000000 : ℝ)) / 2) ≤ (-32476390461361 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-32476390461361 / 10000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (52685642279 / 10000000000000 : ℝ)) / 2) ≤ (-293884715961113 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-293884715961113 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (247462905351 / 50000000000000 : ℝ)) / 2) ≤ (-10647606205457 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-10647606205457 / 4000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log ((((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (453314561379 / 100000000000000 : ℝ)) / 2) ≤ (-241872310625357 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-241872310625357 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log ((((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (200662583153 / 50000000000000 : ℝ)) / 2) ≤ (-55250348842707 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-55250348842707 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log ((((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (338438028731 / 100000000000000 : ℝ)) / 2) ≤ (-50896204882169 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-50896204882169 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log ((((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (52754496323 / 20000000000000 : ℝ)) / 2) ≤ (-37920352349133 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-37920352349133 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log ((((78667711 / 1000000000000 : ℝ) + (664241383483 / 1000000000000 : ℝ)) / 2 - (14825913 / 200000000000 : ℝ) + (173611288997 / 100000000000000 : ℝ)) / 2) ≤ (-89514725762521 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-89514725762521 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (14825913 / 200000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_5 : Uρ (78667711 / 1000000000000 : ℝ) ≤ (-68802371773305424971763039 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (584154217309 / 100000000000000 : ℝ)) / 2) ≤ (-63730431964619 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-63730431964619 / 12500000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (72982921593 / 12500000000000 : ℝ)) / 2) ≤ (-246039995366109 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-246039995366109 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (18209079987 / 3125000000000 : ℝ)) / 2) ≤ (-464004782002453 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-464004782002453 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (28979575783 / 5000000000000 : ℝ)) / 2) ≤ (-17203571424493 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-17203571424493 / 4000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (114639104521 / 20000000000000 : ℝ)) / 2) ≤ (-615739521379 / 156250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-615739521379 / 156250000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (140480979497 / 25000000000000 : ℝ)) / 2) ≤ (-89622333300801 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-89622333300801 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (544111831541 / 100000000000000 : ℝ)) / 2) ≤ (-32484685260499 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-32484685260499 / 10000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (518120180117 / 100000000000000 : ℝ)) / 2) ≤ (-293971572380153 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-293971572380153 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (241209289469 / 50000000000000 : ℝ)) / 2) ≤ (-133141511009423 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-133141511009423 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log ((((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (435595619257 / 100000000000000 : ℝ)) / 2) ≤ (-30246802059183 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-30246802059183 / 12500000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log ((((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (376182302897 / 100000000000000 : ℝ)) / 2) ≤ (-110559065568621 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-110559065568621 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log ((((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (60380761637 / 20000000000000 : ℝ)) / 2) ≤ (-101863280453993 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-101863280453993 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log ((((85815639 / 1000000000000 : ℝ) + (297724389273 / 500000000000 : ℝ)) / 2 - (78667711 / 1000000000000 : ℝ) + (206292575863 / 100000000000000 : ℝ)) / 2) ≤ (-189794847674421 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-189794847674421 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (78667711 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_6 : Uρ (85815639 / 1000000000000 : ℝ) ≤ (-27537256492583409517524091 / 10000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (145843637119 / 25000000000000 : ℝ)) / 2) ≤ (-509965901160711 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-509965901160711 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (291395930763 / 50000000000000 : ℝ)) / 2) ≤ (-246101263928451 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-246101263928451 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (3631463183 / 625000000000 : ℝ)) / 2) ≤ (-92825525541589 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-92825525541589 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (576957009321 / 100000000000000 : ℝ)) / 2) ≤ (-53776611693773 / 12500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-53776611693773 / 12500000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (142262202167 / 25000000000000 : ℝ)) / 2) ≤ (-6159350774199 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-6159350774199 / 1562500000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (55554575401 / 10000000000000 : ℝ)) / 2) ≤ (-358617263815627 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-358617263815627 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (133634962099 / 25000000000000 : ℝ)) / 2) ≤ (-324979387123387 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-324979387123387 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (252026890791 / 50000000000000 : ℝ)) / 2) ≤ (-294111429771023 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-294111429771023 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (462033530669 / 100000000000000 : ℝ)) / 2) ≤ (-66608597176577 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-66608597176577 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log ((((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (203061602527 / 50000000000000 : ℝ)) / 2) ≤ (-242144257743777 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-242144257743777 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log ((((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (83187723551 / 25000000000000 : ℝ)) / 2) ≤ (-885279137127 / 400000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-885279137127 / 400000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log ((((19269871 / 200000000000 : ℝ) + (515561896511 / 1000000000000 : ℝ)) / 2 - (85815639 / 1000000000000 : ℝ) + (29127624991 / 12500000000000 : ℝ)) / 2) ≤ (-40798762177903 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-40798762177903 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (85815639 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_7 : Uρ (19269871 / 200000000000 : ℝ) ≤ (-137799142219212910191367693 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (291112633613 / 50000000000000 : ℝ)) / 2) ≤ (-102029328895607 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-102029328895607 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (72651350619 / 12500000000000 : ℝ)) / 2) ≤ (-246191759587777 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-246191759587777 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (578586007289 / 100000000000000 : ℝ)) / 2) ≤ (-232154651523557 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-232154651523557 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (573054155341 / 100000000000000 : ℝ)) / 2) ≤ (-215198043441887 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-215198043441887 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (281441940241 / 50000000000000 : ℝ)) / 2) ≤ (-394384568726001 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-394384568726001 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (273006170181 / 50000000000000 : ℝ)) / 2) ≤ (-358808515085349 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-358808515085349 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (104022933937 / 20000000000000 : ℝ)) / 2) ≤ (-325179143902933 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-325179143902933 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (482579672559 / 100000000000000 : ℝ)) / 2) ≤ (-147162479155041 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-147162479155041 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (215118943211 / 50000000000000 : ℝ)) / 2) ≤ (-3333381236821 / 1250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-3333381236821 / 1250000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log ((((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (179150615487 / 50000000000000 : ℝ)) / 2) ≤ (-242419856538661 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-242419856538661 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log ((((55761057 / 500000000000 : ℝ) + (86161340883 / 200000000000 : ℝ)) / 2 - (19269871 / 200000000000 : ℝ) + (255637720537 / 100000000000000 : ℝ)) / 2) ≤ (-22167783768353 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-22167783768353 / 10000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (19269871 / 200000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_8 : Uρ (55761057 / 500000000000 : ℝ) ≤ (-34487275926713772248195891 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (72571150447 / 12500000000000 : ℝ)) / 2) ≤ (-510407615234141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-510407615234141 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (144732307887 / 25000000000000 : ℝ)) / 2) ≤ (-123161271760259 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-123161271760259 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (287522418161 / 50000000000000 : ℝ)) / 2) ≤ (-2322861733863 / 500000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-2322861733863 / 500000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (35461796313 / 6250000000000 : ℝ)) / 2) ≤ (-86132434483897 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-86132434483897 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (110777370803 / 20000000000000 : ℝ)) / 2) ≤ (-394656294477163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-394656294477163 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (531983894641 / 100000000000000 : ℝ)) / 2) ≤ (-359090014566083 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-359090014566083 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (99721519743 / 20000000000000 : ℝ)) / 2) ≤ (-2603816178777 / 800000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-2603816178777 / 800000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (112463658007 / 25000000000000 : ℝ)) / 2) ≤ (-147325201314843 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-147325201314843 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (47474320343 / 12500000000000 : ℝ)) / 2) ≤ (-16690320025057 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-16690320025057 / 6250000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log ((((33336783 / 250000000000 : ℝ) + (86772388539 / 250000000000 : ℝ)) / 2 - (55761057 / 500000000000 : ℝ) + (137593620809 / 50000000000000 : ℝ)) / 2) ≤ (-242898879872777 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-242898879872777 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (55761057 / 500000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_9 : Uρ (33336783 / 250000000000 : ℝ) ≤ (-69072398821225269741462211 / 25000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (33336783 / 250000000000 : ℝ) + (36136608051 / 6250000000000 : ℝ)) / 2) ≤ (-510784313415933 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-510784313415933 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (33336783 / 250000000000 : ℝ) + (115127698449 / 20000000000000 : ℝ)) / 2) ≤ (-493023151377121 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-493023151377121 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (33336783 / 250000000000 : ℝ) + (284959795693 / 50000000000000 : ℝ)) / 2) ≤ (-232476791050107 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-232476791050107 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (33336783 / 250000000000 : ℝ) + (894633553 / 160000000000 : ℝ)) / 2) ≤ (-215524822319959 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-215524822319959 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (33336783 / 250000000000 : ℝ) + (270345096987 / 50000000000000 : ℝ)) / 2) ≤ (-19752753975247 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-19752753975247 / 5000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (33336783 / 250000000000 : ℝ) + (255568999769 / 50000000000000 : ℝ)) / 2) ≤ (-179754235465951 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-179754235465951 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (33336783 / 250000000000 : ℝ) + (93188389961 / 20000000000000 : ℝ)) / 2) ≤ (-81482391585243 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-81482391585243 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (33336783 / 250000000000 : ℝ) + (39810168269 / 10000000000000 : ℝ)) / 2) ≤ (-295165171275563 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-295165171275563 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log ((((82548843 / 500000000000 : ℝ) + (269345996903 / 1000000000000 : ℝ)) / 2 - (33336783 / 250000000000 : ℝ) + (292363656669 / 100000000000000 : ℝ)) / 2) ≤ (-16730907743229 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-16730907743229 / 6250000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (33336783 / 250000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_10 : Uρ (82548843 / 500000000000 : ℝ) ≤ (-55358731180530840136613439 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (82548843 / 500000000000 : ℝ) + (2873577257 / 500000000000 : ℝ)) / 2) ≤ (-102267021766431 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-102267021766431 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (82548843 / 500000000000 : ℝ) + (570832224209 / 100000000000000 : ℝ)) / 2) ≤ (-7712141190267 / 1562500000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-7712141190267 / 1562500000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (82548843 / 500000000000 : ℝ) + (562395225637 / 100000000000000 : ℝ)) / 2) ≤ (-465514391457049 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-465514391457049 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (82548843 / 500000000000 : ℝ) + (546948350753 / 100000000000000 : ℝ)) / 2) ≤ (-431623748323373 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-431623748323373 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (82548843 / 500000000000 : ℝ) + (10418233573 / 2000000000000 : ℝ)) / 2) ≤ (-395653244400603 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-395653244400603 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (82548843 / 500000000000 : ℝ) + (119803275347 / 25000000000000 : ℝ)) / 2) ≤ (-180074835531441 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-180074835531441 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (82548843 / 500000000000 : ℝ) + (41386265483 / 10000000000000 : ℝ)) / 2) ≤ (-326651333234869 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-326651333234869 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log ((((53051547 / 250000000000 : ℝ) + (201105762729 / 1000000000000 : ℝ)) / 2 - (82548843 / 500000000000 : ℝ) + (153834437961 / 50000000000000 : ℝ)) / 2) ≤ (-296064918872237 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-296064918872237 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (82548843 / 500000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_11 : Uρ (53051547 / 250000000000 : ℝ) ≤ (-277439851503270994348823573 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (53051547 / 250000000000 : ℝ) + (284780115891 / 50000000000000 : ℝ)) / 2) ≤ (-32009905642177 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-32009905642177 / 6250000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (53051547 / 250000000000 : ℝ) + (281829288133 / 50000000000000 : ℝ)) / 2) ≤ (-494407519293109 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-494407519293109 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (53051547 / 250000000000 : ℝ) + (551075705397 / 100000000000000 : ℝ)) / 2) ≤ (-23318027622183 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-23318027622183 / 5000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (53051547 / 250000000000 : ℝ) + (528367200421 / 100000000000000 : ℝ)) / 2) ≤ (-432499933984901 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-432499933984901 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (53051547 / 250000000000 : ℝ) + (490135569961 / 100000000000000 : ℝ)) / 2) ≤ (-99146281631323 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-99146281631323 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (53051547 / 250000000000 : ℝ) + (213759332799 / 50000000000000 : ℝ)) / 2) ≤ (-361188763936419 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-361188763936419 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (53051547 / 250000000000 : ℝ) + (160730056889 / 50000000000000 : ℝ)) / 2) ≤ (-81983163023259 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-81983163023259 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (53051547 / 250000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_12 : Uρ (496117379 / 2000000000000 : ℝ) ≤ (-277765956494863571604953411 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (496117379 / 2000000000000 : ℝ) + (113126318933 / 20000000000000 : ℝ)) / 2) ≤ (-512790147759887 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-512790147759887 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (496117379 / 2000000000000 : ℝ) + (69770480499 / 12500000000000 : ℝ)) / 2) ≤ (-99009340931301 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-99009340931301 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (496117379 / 2000000000000 : ℝ) + (542329956091 / 100000000000000 : ℝ)) / 2) ≤ (-467016349852693 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-467016349852693 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (496117379 / 2000000000000 : ℝ) + (102760919067 / 20000000000000 : ℝ)) / 2) ≤ (-21659398554181 / 5000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-21659398554181 / 5000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (496117379 / 2000000000000 : ℝ) + (232691497549 / 50000000000000 : ℝ)) / 2) ≤ (-397335560291093 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-397335560291093 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (496117379 / 2000000000000 : ℝ) + (95893395569 / 25000000000000 : ℝ)) / 2) ≤ (-362072824537451 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-362072824537451 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log ((((283911191 / 1000000000000 : ℝ) + (72162863729 / 500000000000 : ℝ)) / 2 - (496117379 / 2000000000000 : ℝ) + (227278349951 / 100000000000000 : ℝ)) / 2) ≤ (-329239395251857 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-329239395251857 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (496117379 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_13 : Uρ (283911191 / 1000000000000 : ℝ) ≤ (-278262784666310605595581841 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (283911191 / 1000000000000 : ℝ) + (11233967281 / 2000000000000 : ℝ)) / 2) ≤ (-513426210380203 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-513426210380203 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (283911191 / 1000000000000 : ℝ) + (13815943483 / 2500000000000 : ℝ)) / 2) ≤ (-9913844635043 / 2000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-9913844635043 / 2000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (283911191 / 1000000000000 : ℝ) + (533464935591 / 100000000000000 : ℝ)) / 2) ≤ (-233841441374363 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-233841441374363 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (283911191 / 1000000000000 : ℝ) + (498842794807 / 100000000000000 : ℝ)) / 2) ≤ (-216948034262553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-216948034262553 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (283911191 / 1000000000000 : ℝ) + (13727093681 / 3125000000000 : ℝ)) / 2) ≤ (-398128191463127 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-398128191463127 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (283911191 / 1000000000000 : ℝ) + (333932455209 / 100000000000000 : ℝ)) / 2) ≤ (-363072197309879 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-363072197309879 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (283911191 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_14 : Uρ (170058951 / 500000000000 : ℝ) ≤ (-139332619353331173773255643 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (170058951 / 500000000000 : ℝ) + (277761338837 / 50000000000000 : ℝ)) / 2) ≤ (-514432406703317 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-514432406703317 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (170058951 / 500000000000 : ℝ) + (6798861441 / 1250000000000 : ℝ)) / 2) ≤ (-124179349829617 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-124179349829617 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (170058951 / 500000000000 : ℝ) + (129828087341 / 25000000000000 : ℝ)) / 2) ≤ (-18750026904013 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-18750026904013 / 4000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (170058951 / 500000000000 : ℝ) + (474492672031 / 100000000000000 : ℝ)) / 2) ≤ (-435051011249263 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-435051011249263 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (170058951 / 500000000000 : ℝ) + (19746425243 / 5000000000000 : ℝ)) / 2) ≤ (-399475778723179 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-399475778723179 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log ((((396324613 / 1000000000000 : ℝ) + (24870259471 / 250000000000 : ℝ)) / 2 - (170058951 / 500000000000 : ℝ) + (118029498831 / 50000000000000 : ℝ)) / 2) ≤ (-365044456109491 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-365044456109491 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (170058951 / 500000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_15 : Uρ (396324613 / 1000000000000 : ℝ) ≤ (-279305183338956206823557363 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (396324613 / 1000000000000 : ℝ) + (109867014619 / 20000000000000 : ℝ)) / 2) ≤ (-103089972499021 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-103089972499021 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (396324613 / 1000000000000 : ℝ) + (267548373761 / 50000000000000 : ℝ)) / 2) ≤ (-497759232949851 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-497759232949851 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (396324613 / 1000000000000 : ℝ) + (504825691487 / 100000000000000 : ℝ)) / 2) ≤ (-234924161488661 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-234924161488661 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (396324613 / 1000000000000 : ℝ) + (448893797661 / 100000000000000 : ℝ)) / 2) ≤ (-27266776881881 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-27266776881881 / 6250000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (396324613 / 1000000000000 : ℝ) + (345028602351 / 100000000000000 : ℝ)) / 2) ≤ (-1603979985187 / 400000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-1603979985187 / 400000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (396324613 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_16 : Uρ (974522519 / 2000000000000 : ℝ) ≤ (-3497376374357506927056083 / 1250000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (974522519 / 2000000000000 : ℝ) + (539297881 / 100000000000 : ℝ)) / 2) ≤ (-517120558965487 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-517120558965487 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (974522519 / 2000000000000 : ℝ) + (104130449447 / 20000000000000 : ℝ)) / 2) ≤ (-124870492500357 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-124870492500357 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (974522519 / 2000000000000 : ℝ) + (480602877843 / 100000000000000 : ℝ)) / 2) ≤ (-117923500429131 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-117923500429131 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (974522519 / 2000000000000 : ℝ) + (202111459627 / 50000000000000 : ℝ)) / 2) ≤ (-219200189839687 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-219200189839687 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log ((((289098953 / 500000000000 : ℝ) + (65851089563 / 1000000000000 : ℝ)) / 2 - (974522519 / 2000000000000 : ℝ) + (24380252969 / 10000000000000 : ℝ)) / 2) ≤ (-404083959233061 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-404083959233061 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (974522519 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_17 : Uρ (289098953 / 500000000000 : ℝ) ≤ (-140299247846894980680558127 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (289098953 / 500000000000 : ℝ) + (529226582707 / 100000000000000 : ℝ)) / 2) ≤ (-518822697665141 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-518822697665141 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (289098953 / 500000000000 : ℝ) + (10119177543 / 2000000000000 : ℝ)) / 2) ≤ (-250626802647187 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-250626802647187 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (289098953 / 500000000000 : ℝ) + (113818568089 / 25000000000000 : ℝ)) / 2) ≤ (-47363740868113 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-47363740868113 / 10000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (289098953 / 500000000000 : ℝ) + (354192158011 / 100000000000000 : ℝ)) / 2) ≤ (-27549910328251 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-27549910328251 / 6250000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (289098953 / 500000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_18 : Uρ (729961631 / 1000000000000 : ℝ) ≤ (-14058144779552195767876503 / 5000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (729961631 / 1000000000000 : ℝ) + (64042150591 / 12500000000000 : ℝ)) / 2) ≤ (-4173896442051 / 800000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-4173896442051 / 800000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (729961631 / 1000000000000 : ℝ) + (240410312339 / 50000000000000 : ℝ)) / 2) ≤ (-252164893905021 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-252164893905021 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (729961631 / 1000000000000 : ℝ) + (204989470167 / 50000000000000 : ℝ)) / 2) ≤ (-238572864726827 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-238572864726827 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (729961631 / 1000000000000 : ℝ) + (49998288017 / 20000000000000 : ℝ)) / 2) ≤ (-445823384073337 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-445823384073337 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (729961631 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_19 : Uρ (1611686987 / 2000000000000 : ℝ) ≤ (-281514737178973769803437117 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (1611686987 / 2000000000000 : ℝ) + (100770327143 / 20000000000000 : ℝ)) / 2) ≤ (-52323054288253 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-52323054288253 / 10000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (1611686987 / 2000000000000 : ℝ) + (467929758299 / 100000000000000 : ℝ)) / 2) ≤ (-790514748327 / 156250000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-790514748327 / 156250000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (1611686987 / 2000000000000 : ℝ) + (192781941227 / 50000000000000 : ℝ)) / 2) ≤ (-479053462430737 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-479053462430737 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log ((((220431339 / 250000000000 : ℝ) + (20954789123 / 500000000000 : ℝ)) / 2 - (1611686987 / 2000000000000 : ℝ) + (883038497 / 500000000000 : ℝ)) / 2) ≤ (-224690642343739 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-224690642343739 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1611686987 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_20 : Uρ (220431339 / 250000000000 : ℝ) ≤ (-2204430428372891296480279 / 781250000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (220431339 / 250000000000 : ℝ) + (247668473679 / 50000000000000 : ℝ)) / 2) ≤ (-262374720884971 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-262374720884971 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (220431339 / 250000000000 : ℝ) + (45480018187 / 10000000000000 : ℝ)) / 2) ≤ (-507574201277309 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-507574201277309 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (220431339 / 250000000000 : ℝ) + (359654618391 / 100000000000000 : ℝ)) / 2) ≤ (-481090032514201 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-481090032514201 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (220431339 / 250000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_21 : Uρ (4047462733 / 4000000000000 : ℝ) ≤ (-56489682990916919911849411 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (4047462733 / 4000000000000 : ℝ) + (480661667763 / 100000000000000 : ℝ)) / 2) ≤ (-527416413606301 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-527416413606301 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (4047462733 / 4000000000000 : ℝ) + (43166368707 / 10000000000000 : ℝ)) / 2) ≤ (-510510579907149 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-510510579907149 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (4047462733 / 4000000000000 : ℝ) + (310653324873 / 100000000000000 : ℝ)) / 2) ≤ (-242486760854649 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-242486760854649 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4047462733 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_22 : Uρ (2284012021 / 2000000000000 : ℝ) ≤ (-282767039638574273823494047 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (2284012021 / 2000000000000 : ℝ) + (465887664991 / 100000000000000 : ℝ)) / 2) ≤ (-53016637124597 / 10000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-53016637124597 / 10000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (2284012021 / 2000000000000 : ℝ) + (407630472531 / 100000000000000 : ℝ)) / 2) ≤ (-256806006794727 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-256806006794727 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (2284012021 / 2000000000000 : ℝ) + (252978777913 / 100000000000000 : ℝ)) / 2) ≤ (-489592260083891 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-489592260083891 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (2284012021 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_23 : Uρ (5088585351 / 4000000000000 : ℝ) ≤ (-35394138455335797124678923 / 12500000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (5088585351 / 4000000000000 : ℝ) + (451005237243 / 100000000000000 : ℝ)) / 2) ≤ (-533005286615477 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-533005286615477 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (5088585351 / 4000000000000 : ℝ) + (23908222601 / 6250000000000 : ℝ)) / 2) ≤ (-103381265538353 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-103381265538353 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log ((((280457333 / 200000000000 : ℝ) + (6432545181 / 250000000000 : ℝ)) / 2 - (5088585351 / 4000000000000 : ℝ) + (17840898517 / 10000000000000 : ℝ)) / 2) ≤ (-495627657474037 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-495627657474037 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (5088585351 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_24 : Uρ (280457333 / 200000000000 : ℝ) ≤ (-283915307968191474970423841 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (280457333 / 200000000000 : ℝ) + (218001640903 / 50000000000000 : ℝ)) / 2) ≤ (-133984965490257 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-133984965490257 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (280457333 / 200000000000 : ℝ) + (356141712279 / 100000000000000 : ℝ)) / 2) ≤ (-520430315886787 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-520430315886787 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (280457333 / 200000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_25 : Uρ (6519108259 / 4000000000000 : ℝ) ≤ (-56834906398966478282910149 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (6519108259 / 4000000000000 : ℝ) + (204726353821 / 50000000000000 : ℝ)) / 2) ≤ (-541322645409771 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-541322645409771 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (6519108259 / 4000000000000 : ℝ) + (305900527883 / 100000000000000 : ℝ)) / 2) ≤ (-105461081175907 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-105461081175907 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (6519108259 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_26 : Uρ (3714534929 / 2000000000000 : ℝ) ≤ (-56895465247786563506496721 / 20000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (3714534929 / 2000000000000 : ℝ) + (382412363143 / 100000000000000 : ℝ)) / 2) ≤ (-109413982560749 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-109413982560749 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (3714534929 / 2000000000000 : ℝ) + (24768606003 / 10000000000000 : ℝ)) / 2) ≤ (-107105763975063 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-107105763975063 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (3714534929 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_27 : Uρ (8339031457 / 4000000000000 : ℝ) ≤ (-142430401946706779596191059 / 50000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (8339031457 / 4000000000000 : ℝ) + (354770276113 / 100000000000000 : ℝ)) / 2) ≤ (-553243760160373 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-553243760160373 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log ((((289031033 / 125000000000 : ℝ) + (3068199571 / 200000000000 : ℝ)) / 2 - (8339031457 / 4000000000000 : ℝ) + (173656768791 / 100000000000000 : ℝ)) / 2) ≤ (-136584420656269 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-136584420656269 / 25000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (8339031457 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_28 : Uρ (289031033 / 125000000000 : ℝ) ≤ (-285707693309385314951570509 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (289031033 / 125000000000 : ℝ) + (326373589283 / 100000000000000 : ℝ)) / 2) ≤ (-559925903286987 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-559925903286987 / 100000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (289031033 / 125000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_29 : Uρ (124379927 / 40000000000 : ℝ) ≤ (-286018759122783173258038489 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (124379927 / 40000000000 : ℝ) + (43314563687 / 20000000000000 : ℝ)) / 2) ≤ (-294753640068249 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-294753640068249 / 50000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (124379927 / 40000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_30 : Uρ (7016246261 / 2000000000000 : ℝ) ≤ (-286249726575931037718699949 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log ((((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 - (7016246261 / 2000000000000 : ℝ) + (147860996517 / 100000000000000 : ℝ)) / 2) ≤ (-122294311157799 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-122294311157799 / 20000000000000 : ℝ) := Uω_le_left (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (7016246261 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_31 : Uρ (1953374043 / 500000000000 : ℝ) ≤ (-286831084198255509109161609 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((8992695531 / 1000000000000 : ℝ) - (1953374043 / 500000000000 : ℝ)) / 4) ≤ (-333378415191191 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 10 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-333378415191191 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1953374043 / 500000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_32 : Uρ (59205077 / 10000000000 : ℝ) ≤ (-286831084198255509109161609 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((8992695531 / 1000000000000 : ℝ) - (1953374043 / 500000000000 : ℝ)) / 4) ≤ (-333378415191191 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 10 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-333378415191191 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (59205077 / 10000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_33 : Uρ (59205079 / 10000000000 : ℝ) ≤ (-286831084198255509109161609 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((8992695531 / 1000000000000 : ℝ) - (1953374043 / 500000000000 : ℝ)) / 4) ≤ (-333378415191191 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 10 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-333378415191191 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (59205079 / 10000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_34 : Uρ (8992695531 / 1000000000000 : ℝ) ≤ (-286831084198255509109161609 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((8992695531 / 1000000000000 : ℝ) - (1953374043 / 500000000000 : ℝ)) / 4) ≤ (-333378415191191 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 10 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-333378415191191 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_35 : Uρ (19572466643 / 2000000000000 : ℝ) ≤ (-286020563914077139609829389 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((19572466643 / 2000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (215999854701 / 100000000000000 : ℝ)) / 2) ≤ (-589678910091003 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-589678910091003 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (19572466643 / 2000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_36 : Uρ (40732008867 / 4000000000000 : ℝ) ≤ (-285849657419784029883406909 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((40732008867 / 4000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (273325213863 / 100000000000000 : ℝ)) / 2) ≤ (-573426242018967 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-573426242018967 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (40732008867 / 4000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_37 : Uρ (1322471389 / 125000000000 : ℝ) ≤ (-285710088820188505697116349 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((1322471389 / 125000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (8135797401 / 2500000000000 : ℝ)) / 2) ≤ (-22406148352079 / 4000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-22406148352079 / 4000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (1322471389 / 125000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_38 : Uρ (4549323561 / 400000000000 : ℝ) ≤ (-285485839281551924431582129 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((4549323561 / 400000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (210802007337 / 50000000000000 : ℝ)) / 2) ≤ (-33676767850731 / 6250000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-33676767850731 / 6250000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (4549323561 / 400000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

lemma U_pt_39 : Uρ (12166846693 / 1000000000000 : ℝ) ≤ (-285306655847742696134579989 / 100000000000000000000000000 : ℝ) := by
  rw [Uρ_eq]
  rw [aρ_1, bρ_1, cρ_1, aρ_2, bρ_2, cρ_2, aρ_3, bρ_3, cρ_3, aρ_4, bρ_4, cρ_4, aρ_5, bρ_5, cρ_5, aρ_6, bρ_6, cρ_6, aρ_7, bρ_7, cρ_7, aρ_8, bρ_8, cρ_8, aρ_9, bρ_9, cρ_9, aρ_10, bρ_10, cρ_10, aρ_11, bρ_11, cρ_11, aρ_12, bρ_12, cρ_12, aρ_13, bρ_13, cρ_13, aρ_14, bρ_14, cρ_14, aρ_15, bρ_15, cρ_15, aρ_16, bρ_16, cρ_16]
  have hL1 : Real.log (((12166846693 / 1000000000000 : ℝ) - ((1953374043 / 500000000000 : ℝ) + (8992695531 / 1000000000000 : ℝ)) / 2 + (51204298249 / 10000000000000 : ℝ)) / 2) ≤ (-521788506721173 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU2 : Uω (1953374043 / 500000000000 : ℝ) (8992695531 / 1000000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-521788506721173 / 100000000000000 : ℝ) := Uω_le_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1
  have hL3 : Real.log (((3068199571 / 200000000000 : ℝ) - (289031033 / 125000000000 : ℝ)) / 4) ≤ (-572689121508323 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 9 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU4 : Uω (289031033 / 125000000000 : ℝ) (3068199571 / 200000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-572689121508323 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL3
  have hL5 : Real.log (((6432545181 / 250000000000 : ℝ) - (280457333 / 200000000000 : ℝ)) / 4) ≤ (-255121302117553 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 8 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU6 : Uω (280457333 / 200000000000 : ℝ) (6432545181 / 250000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-255121302117553 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL5
  have hL7 : Real.log (((20954789123 / 500000000000 : ℝ) - (220431339 / 250000000000 : ℝ)) / 4) ≤ (-732767754151 / 160000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 7 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU8 : Uω (220431339 / 250000000000 : ℝ) (20954789123 / 500000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-732767754151 / 160000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL7
  have hL9 : Real.log (((65851089563 / 1000000000000 : ℝ) - (289098953 / 500000000000 : ℝ)) / 4) ≤ (-205773641193683 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU10 : Uω (289098953 / 500000000000 : ℝ) (65851089563 / 1000000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-205773641193683 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL9
  have hL11 : Real.log (((24870259471 / 250000000000 : ℝ) - (396324613 / 1000000000000 : ℝ)) / 4) ≤ (-184903723234767 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 6 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU12 : Uω (396324613 / 1000000000000 : ℝ) (24870259471 / 250000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-184903723234767 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL11
  have hL13 : Real.log (((72162863729 / 500000000000 : ℝ) - (283911191 / 1000000000000 : ℝ)) / 4) ≤ (-332394599063847 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU14 : Uω (283911191 / 1000000000000 : ℝ) (72162863729 / 500000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-332394599063847 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL13
  have hL15 : Real.log (((201105762729 / 1000000000000 : ℝ) - (53051547 / 250000000000 : ℝ)) / 4) ≤ (-299127444046241 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 5 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU16 : Uω (53051547 / 250000000000 : ℝ) (201105762729 / 1000000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-299127444046241 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL15
  have hL17 : Real.log (((269345996903 / 1000000000000 : ℝ) - (82548843 / 500000000000 : ℝ)) / 4) ≤ (-134933299884173 / 50000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU18 : Uω (82548843 / 500000000000 : ℝ) (269345996903 / 1000000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-134933299884173 / 50000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL17
  have hL19 : Real.log (((86772388539 / 250000000000 : ℝ) - (33336783 / 250000000000 : ℝ)) / 4) ≤ (-244485107162163 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU20 : Uω (33336783 / 250000000000 : ℝ) (86772388539 / 250000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-244485107162163 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL19
  have hL21 : Real.log (((86161340883 / 200000000000 : ℝ) - (55761057 / 500000000000 : ℝ)) / 4) ≤ (-44572980656131 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 4 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU22 : Uω (55761057 / 500000000000 : ℝ) (86161340883 / 200000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-44572980656131 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL21
  have hL23 : Real.log (((515561896511 / 1000000000000 : ℝ) - (19269871 / 200000000000 : ℝ)) / 4) ≤ (-51224479298441 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU24 : Uω (19269871 / 200000000000 : ℝ) (515561896511 / 1000000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-51224479298441 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL23
  have hL25 : Real.log (((297724389273 / 500000000000 : ℝ) - (85815639 / 1000000000000 : ℝ)) / 4) ≤ (-47621959951793 / 25000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU26 : Uω (85815639 / 1000000000000 : ℝ) (297724389273 / 500000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-47621959951793 / 25000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL25
  have hL27 : Real.log (((664241383483 / 1000000000000 : ℝ) - (78667711 / 1000000000000 : ℝ)) / 4) ≤ (-35910449319861 / 20000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU28 : Uω (78667711 / 1000000000000 : ℝ) (664241383483 / 1000000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-35910449319861 / 20000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL27
  have hL29 : Real.log (((89520072139 / 125000000000 : ℝ) - (14825913 / 200000000000 : ℝ)) / 4) ≤ (-5375777321413 / 3125000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU30 : Uω (14825913 / 200000000000 : ℝ) (89520072139 / 125000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-5375777321413 / 3125000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL29
  have hL31 : Real.log (((746637295669 / 1000000000000 : ℝ) - (7174131 / 100000000000 : ℝ)) / 4) ≤ (-167856621058029 / 100000000000000 : ℝ) := by
    refine le_trans (log_le_of_pow_two_upper (by norm_num) 3 11 (by norm_num)) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hU32 : Uω (7174131 / 100000000000 : ℝ) (746637295669 / 1000000000000 : ℝ) (12166846693 / 1000000000000 : ℝ) ≤ (-167856621058029 / 100000000000000 : ℝ) := Uω_le_inside (by norm_num) (by norm_num) hL31
  linarith [hU2, hU4, hU6, hU8, hU10, hU12, hU14, hU16, hU18, hU20, hU22, hU24, hU26, hU28, hU30, hU32]

end Apery
