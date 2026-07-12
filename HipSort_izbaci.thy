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


(*
fun JesteHip2 :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteHip2 l m = (\<forall>i \<in> {0..<m}. najveci3 l i m = i)"
*)

fun SkoroHip2 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"SkoroHip2 l m q = ((\<forall>i \<in> {0..<m} - {q}. najveci3 l i m = i) \<and> (q = 0 \<or> najveci3roditelj l q m = roditelj q))"
                                                                     (*PODRZAVAJUCI USLOV*)

fun JesteSortiran :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteSortiran l m = (\<forall>x \<in> {m..<length l - 1}. l!x \<le> l!(x+1))"

fun invarijanta :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"invarijanta l m = (JesteHip2 l m \<and> JesteSortiran l m \<and> (m \<ge> length l \<or> l ! 0 \<le> l ! m))"


(* BLOK POMOCNIH LEMA *)

lemma izbaci_len:
  assumes "i \<le> length l"
    shows "length (izbaci l i m) = length l"
  by (induction l i m rule: izbaci.induct) (auto simp add: swap_len)

lemma izbaci'_len:
  assumes "i \<le> length l"
      and "i > 1"
    shows "length (izbaci' l i) = length l"
  using izbaci_len swap_len assms
  by (metis izbaci'.simps zero_le)

lemma izbaci_desno:
  assumes "i \<le> length l"
    shows "\<forall>x\<ge>m. izbaci l i m ! x = l!x"
proof (induction l i m rule: izbaci.induct)
  case (1 l i m)
  show ?case 
  proof (cases "i = najveci3 l i m")
    case True
    then show ?thesis 
      by auto
  next
    case False
    with 1 have "\<forall>x\<ge>m. izbaci l i m ! x = swap l i (najveci3 l i m) ! x"
      by auto
    moreover
    from assms have swap_props:
      "\<forall>x\<ge>m. swap l i (najveci3 l i m) ! x = l!x"
      unfolding swap_def
      by auto
    ultimately show ?thesis 
      by auto
  qed
qed

lemma sortiran_jedinicni:
  shows "JesteSortiran l (length l - 1)"
  by auto

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


lemma SkoroHip2_0_swap1:
  assumes "SkoroHip2 l m 0"
    shows "SkoroHip2 (l[0 := x]) m 0"
proof -
  from assms have *: "\<forall>i \<in> {1..<m}. najveci3 l i m = i"
    by auto
  have "\<forall>i \<in> {1..<m}. najveci3 (l[0 := x]) i m = i"
  proof
    fix i
    assume a: "i \<in> {1..<m}"
    
    from a have "l!i = (l[0 := x])!i"
      by auto
    moreover
    from a have "levo i \<ge> m \<or> l!levo i = (l[0 := x])!levo i"
      by auto
    moreover
    from a have "desno i \<ge> m \<or> l!desno i = (l[0 := x])!desno i"
      by auto
    ultimately show "najveci3 (l[0 := x]) i m = i"
      using * a
      by (smt (verit, del_insts) Suc_eq_plus1 add_2_eq_Suc' desno.simps less_eq_Suc_le
          levo.simps linorder_not_less najveci3.elims nle_le rod_levo)
  qed
  then show ?thesis
    by auto
qed

lemma SkoroHip2_0_swap2:
  assumes "SkoroHip2 l m 0"
      and "q \<ge> m"
      and "q < length l"
    shows "SkoroHip2 (l[q := x]) m 0"
proof -
  have *: "\<forall>i. i < length l \<and> i \<noteq> q \<longrightarrow> l!i = (l[q := x])!i"
    by simp
  from assms(1) have **: "\<forall>i \<in> {1..<m}. najveci3 l i m = i"
    by auto
  have "\<forall>i \<in> {1..<m}. najveci3 (l[q := x]) i m = i"
  proof
    fix i
    assume a: "i \<in> {1..<m}"

    from a * assms(2) have "l!i = (l[q := x])!i"
      by auto
    moreover
    from a * assms(2) have "levo i \<ge> m \<or> l!levo i = (l[q := x])!levo i"
      by fastforce
    moreover
    from a * assms(2) have "desno i \<ge> m \<or> l!desno i = (l[q := x])!desno i"
      by fastforce
    ultimately show "najveci3 (l[q := x]) i m = i"
      using ** a
      by (smt (verit, best) Suc_eq_plus1 add_2_eq_Suc' desno.simps less_eq_Suc_le levo.simps linorder_not_less najveci3.elims
          nle_le)
  qed
  then show ?thesis
    by simp
qed

(* sledeca lema je dobijena pomocu Gemini *)
lemma roditelj_induct [case_names 0 rec]:
  fixes P :: "nat \<Rightarrow> bool"
  assumes base: "P 0"
  assumes step: "\<And>x. \<lbrakk>x > 0; P (roditelj x) \<rbrakk> \<Longrightarrow> P x"
  shows "P x"
proof (induction x rule: less_induct)
  case (less x)
  show "P x"
  proof (cases "x = 0")
    case True
    thus "P x" using base by simp
  next
    case False
    hence "x > 0" by simp
    hence "(roditelj x) < x" by simp
    hence "P (roditelj x)" by (rule less.IH)
    thus "P x" using step \<open>x > 0\<close> by simp
  qed
qed

lemma hip_koren_najveci_pomocna:
  assumes "q > 0"
      and "q < m"
      and "m \<le> length l"
    shows "l ! 0 = izbaci l q m ! 0"
  using assms
proof (induction l q m rule: izbaci.induct)
  case (1 l i m)
  then show ?case
  proof(cases "i = najveci3 l i m")
    case True
    then show ?thesis
      by auto
  next
    case False
    with 1 have "swap l i (najveci3 l i m) ! 0 = izbaci (swap l i (najveci3 l i m)) (najveci3 l i m) m ! 0"
      using swap_len[of l i "najveci3 l i m"]
      by simp
    moreover
    from False have "izbaci (swap l i (najveci3 l i m)) (najveci3 l i m) m ! 0 = izbaci l i m ! 0"
      by simp
    moreover
    have "swap l i (najveci3 l i m) ! 0 = l ! 0"
      unfolding swap_def
      by (metis "1.prems"(1) less_or_eq_imp_le linorder_not_less najveci3_dalje nth_list_update_neq)
    ultimately show ?thesis
      by auto
  qed
qed

lemma hip_koren_najveci:
  assumes "JesteHip1 l m"
      and "q < m"
      and "m \<le> length l"
    shows "l ! 0 \<ge> l ! q"
  using assms
proof (induction q rule: roditelj_induct)
  case 0
  then show ?case
    by auto
next
  case (rec x)
  from rec(2-4) have "l ! 0 \<ge> l ! roditelj x"
    by (smt (verit, ccfv_threshold) Nat.lessE diff_Suc_1 diff_is_0_eq div_less div_less_dividend le_eq_less_or_eq
        less_eq_Suc_le numeral_2_eq_2 order_less_trans rec.prems(3) roditelj.simps zero_less_Suc)
  moreover
  from rec(1,3,4) have "l ! roditelj x \<ge> l ! x"
      by simp
  ultimately show ?case
    by simp
qed

lemma koren_posle_izbaci:
  assumes "q < length l"
      and "q > 0"
    shows "izbaci l 0 q ! 0 = l ! 0 \<or> (q > 1 \<and> izbaci l 0 q ! 0 = l ! 1) \<or> (q > 2 \<and> izbaci l 0 q ! 0 = l ! 2)"
proof -
  from assms(1) have swap_props:
      "\<forall>x y. x < q \<and> y < q \<longrightarrow> swap l x y!x = l!y"
      "\<forall>x y. x < q \<and> y < q \<longrightarrow> swap l x y!y = l!x"
      "\<forall>x y. x < q \<and> y < q \<longrightarrow> (\<forall>z. z < length l \<and> z \<noteq> x \<and> z \<noteq> y \<longrightarrow> swap l x y!z = l!z)"
    unfolding swap_def
    by (metis le_trans linorder_not_less list_update_id nat_less_le nth_list_update_eq nth_list_update_neq,
        metis nat_less_le length_list_update nth_list_update linorder_not_less le_trans, simp)

  from assms(2) have "(q = 1 \<or> q = 2) \<or> q > 2"
    by auto
  then show ?thesis
  proof
    assume "q = 1 \<or> q = 2"
    then show ?thesis
    proof
      assume "q = 1"
      then show ?thesis
        by auto
    next
      assume a: "q = 2"
      show ?thesis
      proof (cases "najveci3 l 0 q = 0")
        case True
        then show ?thesis
          by auto
      next
        case False
        with a have "najveci3 l 0 q = 1"
          by auto
        then have tv1: "swap l 0 1 ! 0 = l ! 1"
          unfolding swap_def
          by (metis False assms(1,2) nth_list_update_eq nth_list_update_neq order_less_trans)
        with a False have "izbaci l 0 q = swap l 0 1"
          by auto
        with tv1 show ?thesis
          by auto
      qed
    qed
  next
    assume a: "q > 2"
    show ?thesis
    proof (cases "najveci3 l 0 q = 0")
        case True
        then show ?thesis
          by auto
      next
        case False
        with assms(1,2) have tv1: "swap l 0 (najveci3 l 0 q) ! 0 = l ! 1 \<or> swap l 0 (najveci3 l 0 q) ! 0 = l ! 2"
          unfolding swap_def False assms(1,2)
          by (smt (verit, ccfv_SIG) One_nat_def Suc_eq_plus1 add_2_eq_Suc' desno.simps diff_is_0_eq
              le_add_diff_inverse2 le_numeral_extra(3) levo.simps mult_2 najveci3.elims nth_list_update_eq 
              nth_list_update_neq numeral_2_eq_2 order_less_trans)
        with False a assms(1) show ?thesis
          using hip_koren_najveci_pomocna[of "najveci3 l 0 q" q "swap l 0 (najveci3 l 0 q)"]
          using swap_len[of l 0 "najveci3 l 0 q"]
          by simp
      qed
  qed
qed


(* BLOK MSET LEMA *)

lemma izbaci_korak_mset:
  assumes "i < m"
      and "m \<le> length l"
    shows "mset (izbaci l i m) = mset l"
  using assms
  by (induction l i m rule: izbaci.induct) (auto simp add: swap_mset swap_len)

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

theorem izbaciSve_korektnost_mset:
  shows "mset (izbaciSve l (length l)) = mset l"
  using izbaciSve_korak_mset
  by (metis nat_less_le linorder_not_less)


(* BLOK HIP & SORT LEMA *)

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
    assumes "invarijanta l q"
        and "q > 1"
        and "q \<le> length l"
      shows "invarijanta (izbaci' l q) (q-1)"
proof -
  from assms(2-3) have swap_props:
      "swap l 0 (q-1)!(q-1) = l!0"
      "swap l 0 (q-1)!0     = l!(q-1)"
      "\<forall>x. x < length l \<and> x \<noteq> 0 \<and> x \<noteq> (q-1) \<longrightarrow> swap l 0 (q-1)!x = l!x"
    unfolding swap_def
    by (simp, metis diff_is_0_eq diff_zero linorder_not_less not_less_iff_gr_or_eq
        nth_list_update_eq nth_list_update_neq, simp)

  from assms(1) have hip2: "JesteHip2 l q"
    by auto
  with JesteHipEkvDef have hip1: "JesteHip1 l q"
    by auto

  from assms(2,3) have len: "length l > 1"
    by simp

  let ?izb_sw_l = "izbaci (swap l 0 (q - 1)) 0 (q-1)"
  from assms(2,3) have izb': "?izb_sw_l = izbaci' l q"
    by simp

  have "JesteHip2 (izbaci' l q) (q-1)"
  proof -
    from assms(2) hip1 have "JesteHip1 l (q-1)"
      by auto
    with JesteHipEkvDef have "JesteHip2 l (q-1)"
      by auto
    then have "SkoroHip2 l (q-1) 0"
      by auto
    with assms(2,3) have "SkoroHip2 (swap l 0 (q - 1)) (q-1) 0"
      using SkoroHip2_0_swap1 SkoroHip2_0_swap2 swap_step_by_step
      by (metis (no_types, lifting) linorder_not_less list_update_beyond nle_le)
    with assms(2,3) have "JesteHip2 ?izb_sw_l (q-1)"
      using izbaci_korak_hip[of "swap l 0 (q - 1)" "q-1" 0]
      by (metis diff_le_self less_imp_diff_less nat_less_le swap_len zero_less_diff)
    with izb' show ?thesis
      by auto
  qed

  moreover
  have "JesteSortiran (izbaci' l q) (q-1)"
  proof -
    from assms(1) have tvs1: "\<forall>x \<in> {q..<length l - 1}. l!x \<le> l!(x+1)"
      by auto

    from izbaci'_len[of q l] izb' assms(2,3) have len_izb_sw_l: "length ?izb_sw_l = length l"
      by simp

    from swap_props(3) assms(2) have swap3': "\<forall>x. q \<le> x \<and> x < length l \<longrightarrow> swap l 0 (q-1)!x = l!x"
      by auto
    then have tvs2: "\<forall>x. q \<le> x \<and> x < length l \<longrightarrow> ?izb_sw_l ! x = l!x"
      using swap_len izbaci_desno
      by (metis diff_le_self le_trans less_Suc_eq_0_disj less_imp_Suc_add nat_less_le)
    with tvs1 have tvs3: "\<forall>x \<in> {q..<length ?izb_sw_l - 1}. ?izb_sw_l!x \<le> ?izb_sw_l!(x+1)"
      using len_izb_sw_l 
      by (metis (full_types) add.commute atLeastLessThan_iff less_diff_conv not_less_iff_gr_or_eq trans_le_add2
          trans_less_add2)

    show ?thesis
    proof (cases "q \<ge> length l")
      case True
      with assms(3) have "q = length l"
        by simp
      with assms(2) show ?thesis
        using izbaci'_len sortiran_jedinicni
        by (metis le_refl)
    next
      case False      
      have "\<forall>x \<in> {q-1..<length ?izb_sw_l - 1}. ?izb_sw_l!x \<le> ?izb_sw_l!(x+1)"
      proof 
        fix x
        assume a: "x \<in> {q - 1..<length (izbaci (swap l 0 (q - 1)) 0 (q - 1)) - 1}"
        show "?izb_sw_l ! x \<le> ?izb_sw_l ! (x + 1)"
        proof (cases "x \<le> q - 1")
          case True
          with a have "x = q - 1"
            by (meson atLeastLessThan_iff nle_le)
          with assms(1,2) tvs2 False show "?izb_sw_l!x \<le> ?izb_sw_l!(x+1)"
            using swap_props(1) izbaci_desno
            by (metis invarijanta.simps le_add_diff_inverse2 le_zero_eq linorder_not_less nle_le)
        next
          case False
          with a have "x\<in>{q..<length (izbaci (swap l 0 (q - 1)) 0 (q - 1)) - 1}"
            by (meson atLeastLessThan_iff dec_less_imp_less_eq linorder_not_less)
          with tvs3 show ?thesis 
            by metis
        qed
      qed
      with tvs3 izb' show ?thesis
        by (metis JesteSortiran.simps)
    qed
  qed

  moreover
  have "q - 1 < length (izbaci' l q) \<longrightarrow> (izbaci' l q) ! 0 \<le> (izbaci' l q) ! (q-1)"
  proof
    assume a: "q - 1 < length (izbaci' l q)"
    have izbacen: "?izb_sw_l ! (q - 1) = l ! 0"
      by (metis bot_nat_0.extremum izbaci_desno le_refl swap_props(1))
    
    from hip2 have "\<forall>i. i < q \<longrightarrow> najveci3 l i q = i"
      by auto    
    with assms(2) have "najveci3 l 0 q = 0"
      by blast
    with assms(2) have levo_desno: "l ! 0 \<ge> l ! 1 \<and> (q = 2 \<or> l ! 0 \<ge> l ! 2)"
      by (metis One_nat_def Suc_eq_plus1 add_2_eq_Suc' desno.simps le_eq_less_or_eq less_eq_Suc_le levo.simps mult_zero_right
          one_add_one rod_desno rod_levo roditelj_je_najveci3)
    from hip1 assms(2,3) have koren: "l ! 0 \<ge> l ! (q-1)"
      using hip_koren_najveci
      by auto

    have izb'_0: "(q > 2 \<and> ?izb_sw_l!0 = l!1) \<or> (q > 3 \<and> ?izb_sw_l!0 = l!2) \<or> ?izb_sw_l!0 = l!(q-1)"
    proof -
      have s1: "q \<le> 2 \<or> (swap l 0 (q - 1))!1 = l!1"
        using swap_props(3) assms(2) len
        by auto
      have s2: "q \<le> 3 \<or> (swap l 0 (q - 1))!2 = l!2"
        using swap_props(3) assms(2,3) len
        by (metis (no_types, lifting) One_nat_def Suc_pred less_Suc_eq_le nat_less_le nle_le numeral_2_eq_2 numeral_3_eq_3)

      from a assms(2,3) swap_props(2) s1 s2 show ?thesis
        using koren_posle_izbaci[of "q-1" "swap l 0 (q - 1)"] izbaci'_len
        by (metis (no_types, lifting) Suc_eq_plus1  less_diff_conv nat_less_le nle_le numeral_3_eq_3 one_add_one swap_len zero_less_diff)
    qed
    
    from izbacen levo_desno koren izb'_0 assms(2) have "?izb_sw_l!0 \<le> ?izb_sw_l!(q-1)"
      by presburger
    then show "izbaci' l q ! 0 \<le> izbaci' l q ! (q - 1)"
      by auto
  qed
  then have "q - 1 \<ge> length (izbaci' l q) \<or> (izbaci' l q) ! 0 \<le> (izbaci' l q) ! (q-1)" 
    by presburger

  ultimately show ?thesis
    using invarijanta.simps by blast
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
            by (metis "1.prems"(1,3) \<open>q = 2\<close> dual_order.refl invarijanta.elims(2) izbaci'_len izbaciSve.simps)
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

end