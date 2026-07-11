theory HipSort_izbaci
  imports Main HipSort_zajednicko
begin

function izbaci :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list" where
"izbaci l i m = (if i = (najveci3 l i m) then l
                 else izbaci (swap l i (najveci3 l i m)) (najveci3 l i m) m)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(l, i, m). (m - i))") (auto simp add: if_split)

fun izbaci' :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"izbaci' l i = izbaci (swap l 0 (i-1)) 0 (i-1)"

fun izbaciSve :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"izbaciSve l i = (if i \<le> 1 then l
                  else izbaciSve (izbaci' l i) (i-1))"



fun JesteHip2 :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteHip2 l m = (\<forall>i \<in> {0..<m}. najveci3 l i m = i)"

fun SkoroHip2 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"SkoroHip2 l m q = ((\<forall>i \<in> {0..<m} - {q}. najveci3 l i m = i) \<and> (q = 0 \<or> najveci3roditelj l q m = roditelj q))"
                                                                     (*PODRZAVAJUCI USLOV*)

fun JesteSortiran :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteSortiran l m = (\<forall>x \<in> {m..<length l - 1}. l!x \<le> l!(x+1))"

fun invarijanta :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"invarijanta l m = (JesteHip2 l m \<and> JesteSortiran l m \<and> (m \<ge> length l \<or> l ! 0 \<le> l ! m))"

lemma izbaci_len:
  assumes "i \<le> length l"
    shows "length (izbaci l i m) = length l"
  by (induction l i m rule: izbaci.induct) auto

lemma izbaci'_len:
  assumes "i \<le> length l"
      and "i > 1"
    shows "length (izbaci' l i) = length l"
  using izbaci_len assms
  by force

lemma najveci3_deca:
  assumes "najveci3 l q m \<noteq> q"
  shows "najveci3 l q m = levo q \<or> najveci3 l q m = desno q"
  using assms
  by (meson najveci3.elims)

lemma najveci3_dalje:
  assumes "najveci3 l q m \<noteq> q"
  shows "najveci3 l q m > q"
  using assms najveci3_deca
  by fastforce

lemma deca_razl:
  assumes "q \<noteq> 0"
    shows "levo q \<noteq> q"
      and "desno q \<noteq> q"
  by auto

lemma swap_lemma_izbaci:
  assumes "p < m"
      and "q < p"
      and "m \<le> length l"
    shows "l!p = (swap l q p)!q"
      and "(swap l q p)!p = l!q"
      and "\<forall>x. x < m \<and> x \<noteq> q \<and> x \<noteq> p \<longrightarrow> (swap l q p)!x = l!x"
proof -
  from assms show "l!p = (swap l q p)!q"
    unfolding swap_def
    by auto
next
  from assms show "(swap l q p)!p = l!q"
    unfolding swap_def
    by auto
next
  from assms show "\<forall>x. x < m \<and> x \<noteq> q \<and> x \<noteq> p \<longrightarrow> (swap l q p)!x = l!x"
    unfolding swap_def
    by auto
qed

lemma izbaci_SkoroHip2:
  assumes "SkoroHip2 l m q"
      and "q < m"
      and "najveci3 l q m \<noteq> q"
      and "nl = swap l q (najveci3 l q m)"
      and "m \<le> length l"
    shows "SkoroHip2 nl m (najveci3 l q m)"
proof -
  from assms(2-5) have swap_props:
      "nl!q = l!najveci3 l q m"
      "nl!najveci3 l q m = l!q"
      "\<forall>x. x < m \<and> x \<noteq> q \<and> x \<noteq> najveci3 l q m \<longrightarrow> nl!x = l!x"
    unfolding swap_def
    by auto

  from assms(1) have tv1: "\<forall>i \<in> {0..<m} - {q}. najveci3 l i m = i"
    by simp

  have "q \<noteq> 0 \<longrightarrow> najveci3 nl (roditelj q) m = roditelj q"
  proof
    assume "q \<noteq> 0"
    with assms(1) have tv2: "najveci3roditelj l q m = roditelj q"
      by simp

    from \<open>q \<noteq> 0\<close> assms have "roditelj q < m" "roditelj q \<noteq> q"
      by (simp, simp)
    with tv1 assms have plv: "najveci3 l (roditelj q) m = roditelj q"
      by simp

    from \<open>q \<noteq> 0\<close> have "q = levo (roditelj q) \<or> q = desno (roditelj q)"
      by auto
    then show "najveci3 nl (roditelj q) m = roditelj q"
    proof
      assume a: "q = levo (roditelj q)"

      with assms(2,3) have ltv1: "desno (roditelj q) < m"
        by (metis (no_types, lifting) add_2_eq_Suc' add_Suc_right bot_nat_0.extremum_strict desno.simps
            div_less_dividend le_eq_less_or_eq less_eq_Suc_le levo.simps najveci3.simps nat_0_less_mult_iff nat_arith.rule0
            nonzero_mult_div_cancel_left not_less_iff_gr_or_eq plus_1_eq_Suc)
      moreover
      from ltv1 plv have "l!roditelj q \<ge> l!desno (roditelj q)"
        by (smt (verit, best) najveci3.simps)
      moreover
      from a have "desno (roditelj q) \<noteq> q"
        by simp
      moreover
      have "desno (roditelj q) \<noteq> najveci3 l q m"
        by (metis assms(3) plv rod_desno najveci3_deca rod_levo)
      moreover
      from a have ltv3: "roditelj q \<noteq> q \<and> roditelj q \<noteq> najveci3 l q m"
        by simp
      ultimately have l_zln: "nl!roditelj q \<ge> nl!desno (roditelj q)"  (*tamno zelena grana*)
        using \<open>roditelj q < m\<close> swap_props(3)
        by presburger

      from tv2 have "l!roditelj q \<ge> l!najveci3 l q m"
        by (smt (verit, best) assms(3) najveci3.elims najveci3roditelj.elims)
      with swap_props(1,3) have l_plv: "nl!roditelj q \<ge> nl!q"
        using \<open>roditelj q < m\<close> ltv3
        by presburger

      from l_zln l_plv a show "najveci3 nl (roditelj q) m = roditelj q"
        by auto
    next
      assume a: "q = desno (roditelj q)"

      with assms(2,3) have dtv1: "levo (roditelj q) < m"
        by auto
      moreover
      from dtv1 plv have "l!roditelj q \<ge> l!levo (roditelj q)"
        by (smt (verit, best) najveci3.simps)
      moreover
      from a have "levo (roditelj q) \<noteq> q"
        by simp
      moreover
      have "levo (roditelj q) \<noteq> najveci3 l q m"
        by (metis assms(3) plv rod_desno najveci3_deca rod_levo)
      moreover
      from a have dtv3: "roditelj q \<noteq> q \<and> roditelj q \<noteq> najveci3 l q m"
        by simp
      ultimately have d_zln: "nl!roditelj q \<ge> nl!levo (roditelj q)"  (*tamno zelena grana*)
        using \<open>roditelj q < m\<close> swap_props(3)
        by presburger

      from tv2 have "l!roditelj q \<ge> l!najveci3 l q m"
        by (smt (verit, best) assms(3) najveci3.elims najveci3roditelj.elims)
      with swap_props(1,3) have d_plv: "nl!roditelj q \<ge> nl!q"
        using \<open>roditelj q < m\<close> dtv3
        by presburger

      from d_zln d_plv a show "najveci3 nl (roditelj q) m = roditelj q"
        by auto
    qed    
  qed
  then have plv_zln: "q = 0 \<or> najveci3 nl (roditelj q) m = roditelj q"
    by metis

  from assms(3) have "(najveci3 l q m) = levo q \<or> (najveci3 l q m) = desno q"
    by (metis najveci3.elims)
  then have crv: "najveci3 nl q m = q"
  proof
    assume a: "najveci3 l q m = levo q"
    show ?thesis
    proof (cases "desno q \<ge> m")
      case True
      with a swap_props(1,2) show ?thesis
        by fastforce
    next
      case False
      from a assms(4) have "nl = swap l q (levo q)"
        by simp
      from a False have "l!levo q \<ge> l!q" "l!levo q \<ge> l!desno q"
        by (smt (verit, best) najveci3.elims, smt (verit, best) linorder_not_less najveci3.elims)
      with swap_props a False have "nl!q \<ge> nl!levo q" "nl!q \<ge> nl!desno q"
        by (metis, force)
      then show ?thesis
        by auto
    qed
  next
    assume a: "najveci3 l q m = desno q"
    from a assms(4) have "nl = swap l q (desno q)"
      by simp
    from a assms(3) have "l!desno q \<ge> l!q" "l!desno q \<ge> l!levo q"
      by (smt (verit, best) najveci3.elims, smt (verit, best) najveci3.elims)
    with swap_props assms(3) a have "nl!q \<ge> nl!desno q" "nl!q \<ge> nl!levo q"
       by (simp, smt (verit, best) Suc_eq_plus1 add_2_eq_Suc' desno.simps less_eq_Suc_le levo.simps najveci3.elims nat_less_le)
    then show ?thesis
      by auto
  qed

  have "najveci3roditelj nl (najveci3 l q m) m = q"
  proof - 
    from assms(3) have "najveci3 l q m < m"
       by fastforce
    with tv1 assms(3) have "najveci3 l (najveci3 l q m) m = (najveci3 l q m)"
      by simp
    with swap_props(1) assms(3,4) show ?thesis
      using rod_desno rod_levo swap_def
      by (smt (verit) najveci3.elims najveci3roditelj.elims nth_list_update_neq)
  qed
  then have splv: "najveci3roditelj nl (najveci3 l q m) m = roditelj (najveci3 l q m)"
    using \<open>najveci3 l q m = levo q \<or> najveci3 l q m = desno q\<close> rod_desno rod_levo 
    by presburger

  have szln: "(\<forall>i \<in> {0..<m} - {roditelj q, q, najveci3 l q m}. najveci3 nl i m = i)"
  proof
    fix i
    assume a: "i \<in> {0..<m} - {roditelj q, q, najveci3 l q m}"
    with tv1 have at1: "najveci3 l i m = i"
      by auto
    moreover
    from a swap_props(3) have "l!i = nl!i"
      by auto
    moreover
    from a swap_props(3) have "levo i < m \<longrightarrow> l!levo i = nl!levo i"
      by auto
    moreover
    from a swap_props(3) have "desno i < m \<longrightarrow> l!desno i = nl!desno i"
      by auto
    ultimately show "najveci3 nl i m = i"
      by (smt (verit, best) One_nat_def add_Suc_right desno.simps le_eq_less_or_eq less_eq_Suc_le levo.simps najveci3.elims
          numeral_2_eq_2)
  qed

  from plv_zln crv szln have "\<forall>i \<in> {0..<m} - {najveci3 l q m}. najveci3 nl i m = i"
    by (metis Diff_iff insert_iff mult_2 nat_arith.rule0 nonzero_mult_div_cancel_left not_less_iff_gr_or_eq
        numeral_2_eq_2 roditelj.simps zero_diff zero_less_Suc)
  with splv show ?thesis
    by auto
qed

lemma izbaci_JesteHip2:
  assumes "SkoroHip2 l m q"
      and "najveci3 l q m = q"
    shows "JesteHip2 l m"
proof -
  from assms(1) have "\<forall>i \<in> {0..<m} - {q}. i = najveci3 l i m"
    by auto
  with assms(2) have "\<forall>i \<in> {0..<m}. i = najveci3 l i m"
    by fastforce
  then show ?thesis
    by auto
qed

lemma izbaci_korak_hip:
  assumes "SkoroHip2 l m q"
      and "q < m"
      and "m \<le> length l"
    shows "JesteHip2 (izbaci l q m) m"
  using assms
proof (induction l q m rule: izbaci.induct)
  case (1 l i m)
  show ?case
  proof (cases "najveci3 l i m \<noteq> i")
    case True
    with 1 show ?thesis
      using izbaci_SkoroHip2[of l m i] swap_len[of l i "najveci3 l i m"]
      by (smt (verit, best) One_nat_def add_le_cancel_left desno.simps izbaci.simps le_trans less_eq_Suc_le levo.simps
          linorder_not_less najveci3.simps nless_le numeral_2_eq_2)
  next
    case False
    with 1 show ?thesis
      using izbaci_JesteHip2[of l m i]
      by (metis izbaci.simps)
  qed
qed

lemma izbaci'_invarijanta:
    assumes "invarijanta l q"         (* JesteHip2 l q \<and> JesteSortiran l q \<and> l ! 0 \<le> l ! q *)
        and "q > 1"
        and "q \<le> length l"
      shows "invarijanta (izbaci' l q) (q-1)"   
                                     (* JesteHip2 nl (q-1) \<and> JesteSortiran nl (q-1) \<and> l ! 0 \<le> l ! (q-1) *)
proof -
  show ?thesis
    sorry



(*
  from assms(1) have tv1: "\<forall>i \<in> {0..<q}. najveci3 l i q = i"
    by auto
  with assms(2) have tv1': "najveci3 l (roditelj (q-1)) q = roditelj (q-1)"
    by auto
  have tv1'': "\<forall>i \<in> {0..<q-1}. najveci3 l i (q-1) = i"
  proof -
    from assms(2) have assms2': "q \<noteq> 0"
      by auto
    with tv1' have "najveci3 l (roditelj (q-1)) (q-1) = roditelj (q-1)"
      by (smt (verit, best) add_diff_inverse_nat less_Suc_eq less_one najveci3.simps plus_1_eq_Suc)

    from assms2' tv1 have "\<forall>i \<in> {0..<q} - {roditelj (q-1)}. najveci3 l i (q-1) = i"
      by (smt (verit) Diff_iff add_diff_inverse_nat less_Suc_eq less_one najveci3.simps plus_1_eq_Suc)

    with tv1 tv1' assms2' have "\<forall>i \<in> {0..<q}. najveci3 l i (q-1) = i"
      by (smt (verit, best) add_diff_inverse_nat less_Suc_eq less_one najveci3.simps plus_1_eq_Suc)
    then show ?thesis
      by simp
  qed
  have "\<forall>x \<in> {1..<q-1}. swap l 0 (q - 1) ! x = l ! x"
    using swap_lemma_izbaci(3)[of "q-1" q "0" l] assms(3)
    by auto
  with tv1'' have "\<forall>i \<in> {1..<q-1}. najveci3 (swap l 0 (q-1)) i (q-1) = i"
    sorry
  then have "SkoroHip2 (swap l 0 (q-1)) (q-1) 0"
    by auto
  with assms(3) have thesis1: "JesteHip2 (izbaci (swap l 0 (q-1)) 0 (q-1)) (q-1)"
    using izbaci_korak_hip[of "swap l 0 (q-1)" "q-1" 0]
    unfolding swap_def
    by auto

  from assms(1) have "JesteSortiran l q"
    by auto
  with assms(2,3) have tv2: "JesteSortiran (swap l 0 (q-1)) q"
    sorry
  from assms(1) have "l ! 0 \<le> l ! q"
    by auto
  with assms(2,3) have tv3: "(swap l 0 (q-1)) ! (q-1) \<le> (swap l 0 (q-1)) ! q"
    unfolding swap_def
    by simp
  with tv2 have "JesteSortiran (swap l 0 (q-1)) (q-1)"
    sorry
*)
qed


lemma izbaciSve_korak_sort:
  assumes "q \<le> length l"
      and "invarijanta l q"
      and "q > 1"
    shows "JesteSortiran (izbaciSve l q) 0"
  using assms
proof (induction l q  rule: izbaciSve.induct)
  case (1 l q)
  show ?case
  proof (cases "q \<le> 2")
    case True
    with 1(4) have "q = 2"
      by auto

    from 1(2-4) have tv: "invarijanta (izbaci' l 2) 1"
      using izbaci'_invarijanta[of l q] \<open>q = 2\<close>
      by simp
    
    have "\<forall>x \<in> {0..<length (izbaciSve (izbaci' l 2) 1) - 1}. (izbaciSve (izbaci' l 2) 1)!x \<le> (izbaciSve (izbaci' l 2) 1)!(x+1)"
    proof
      fix x
      assume a: "x \<in> {0..<length (izbaciSve (izbaci' l 2) 1) - 1}"
      show "izbaciSve (izbaci' l 2) 1 ! x \<le> izbaciSve (izbaci' l 2) 1 ! (x + 1)"
      proof (cases "x = 0")
        case True
        then show ?thesis
        proof (cases "length l \<le> 1")
          case True
          then show ?thesis
            using "1.prems"(1) \<open>q = 2\<close> by linarith
        next
          case False
          with tv have "(izbaciSve (izbaci' l 2) 1) ! 0 \<le> (izbaciSve (izbaci' l 2) 1) ! 1"
            by auto
          with True show ?thesis 
            by simp
        qed
        next
          case False
          from tv have "JesteSortiran (izbaciSve (izbaci' l 2) 1) 1"
            by auto
          with False a have "(izbaciSve (izbaci' l 2) 1) ! x \<le> (izbaciSve (izbaci' l 2) 1) ! (x+1)"
            by simp
        then show ?thesis
          by simp
      qed
    qed
    with \<open>q = 2\<close> show ?thesis
      by simp
  next
    case False
    from 1 have tv1: "q - 1 \<le> length (izbaci' l q)"
      using izbaci'_len[of q l]
      by presburger

    from 1 have "invarijanta (izbaci' l q) (q-1)"
      using izbaci'_invarijanta[of l q]
      using linorder_not_less by blast
    with tv1 1 False have tv2: "JesteSortiran (izbaciSve (izbaci' (izbaci' l q) (q - 1)) (q - 1 - 1)) 0"    
      by (metis "1.IH" linorder_not_less diff_is_0_eq izbaciSve.elims numeral_2_eq_2 cancel_comm_monoid_add_class.diff_cancel nat_less_le plus_1_eq_Suc diff_diff_eq)
    with False tv2 have "izbaciSve (izbaci' (izbaci' l q) (q - 1)) (q - 1 - 1)
                     = izbaciSve (izbaci' l q) (q - 1)"
      by (metis One_nat_def diff_diff_eq diff_is_0_eq izbaciSve.simps numeral_2_eq_2 plus_1_eq_Suc)
    with tv2 1(4) show ?thesis
      by (metis  izbaciSve.simps linorder_not_less)
  qed
qed


theorem izbaciSve_korektnost_hip:
  assumes "JesteHip2 l (length l)"
  shows "JesteSortiran (izbaciSve l (length l)) 0"
proof (cases "length l < 1")
  case True
  then show ?thesis
    by auto
next
  case False
  from assms(1) have "invarijanta l (length l)"
    by auto
  with False assms show ?thesis
    using izbaciSve_korak_sort[of "length l" l]
    by fastforce
qed


lemma izbaci_korak_mset:
  assumes "i < m"
      and "m \<le> length l"
    shows "mset (izbaci l i m) = mset l"
  using assms
  by (induction l i m rule: izbaci.induct, auto simp add: swap_mset)

lemma izbaci'_mset:
  assumes "i \<le> length l"
      and "i > 1"
    shows "mset (izbaci' l i) = mset l"
  using assms swap_mset izbaci_korak_mset[of 0 "i-1" "(swap l 0 (i-1))"] swap_len[of l 0 "i-1"]
  by (metis (mono_tags, lifting) diff_less izbaci'.simps le_eq_less_or_eq order_le_less_trans zero_less_diff
      zero_less_one)

lemma izbaciSve_korak_mset:
  assumes "i \<le> length l"
    shows "mset (izbaciSve l i) = mset l"
  using assms
  by (induction l i rule: izbaciSve.induct, metis izbaci_len izbaci'_mset izbaciSve.elims swap_len 
      less_imp_diff_less linorder_not_less izbaci'.simps diff_is_0_eq nat_less_le)

(* TEOREMA KOJU TREBA ISKORISTITI NA KRAJU *)
theorem izbaciSve_korektnost_mset:
  shows "mset (izbaciSve l (length l)) = mset l"
  using izbaciSve_korak_mset
  by (metis nat_less_le linorder_not_less)

end