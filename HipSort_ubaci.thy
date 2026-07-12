theory HipSort_ubaci
  imports Main HipSort_zajednicko
begin

fun ubaci :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"ubaci l i = 
   (if i = 0 \<or> l ! (roditelj i) \<ge> l ! i then l 
    else ubaci (swap l i (roditelj i)) (roditelj i))"

lemma ubaci_len:
  assumes "i < length l"
    shows "length (ubaci l i) = length l"
  by (induction l i rule: ubaci.induct) (auto simp add: swap_len)

function ubaciSve :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"ubaciSve l i = (if i \<ge> length l then l 
                 else ubaciSve (ubaci l i) (i+1))"
  by pat_completeness auto
termination
  using ubaci_len
  by (relation "measure (\<lambda>(l, i). (length l - i))") auto


(*
fun JesteHip1 :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteHip1 l m = (\<forall>i \<in> {1..<m}. l ! roditelj i \<ge> l ! i)"
*)

fun SkoroHip1 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"SkoroHip1 l m q = ((\<forall>i \<in> {1..<m} - {q}. l!roditelj i \<ge> l!i) \<and> (q = 0 \<or> najveci3roditelj l q m = roditelj q))"
                                                                        (*PODRZAVAJUCI USLOV*)

(* BLOK POMOCNIH LEMA *)

lemma ubaciSve_len:
  shows "length (ubaciSve l i) = length l"
  using ubaci_len
  by (induction l i rule: ubaciSve.induct) auto


(* BLOK MSET LEMA *)

lemma ubaci_korak_mset:
  assumes "i < length l"
    shows "mset (ubaci l i) = mset l"
  using assms
  by (induction l i rule: ubaci.induct) (auto simp add: swap_mset swap_len)
  
lemma ubaciSve_korak_mset:
  shows "mset (ubaciSve l i) = mset l"
  using ubaci_korak_mset
  by (induction l i rule: ubaciSve.induct) auto

theorem ubaciSve_korektnost_mset:
  shows "mset (ubaciSve l 0) = mset l"
  using ubaciSve_korak_mset
  by auto


(* BLOK HIP LEMA *)

lemma ubaci_SkoroHip1:
  assumes "SkoroHip1 l m q"
      and "q \<noteq> 0"
      and "q < m" 
      and "l ! roditelj q < l ! q"
      and "nl = swap l q (roditelj q)"
      and "m \<le> length l"
    shows "SkoroHip1 nl m (roditelj q)"
proof -
  from assms(2,3,5,6) have swap_props: 
      "l!roditelj q = nl!q"
      "nl!roditelj q = l!q"
      "\<forall>x. x < m \<and> x \<noteq> q \<and> x \<noteq> roditelj q \<longrightarrow> nl!x = l!x"
      "\<forall>x. x < m \<and> x \<noteq> 0 \<and> x \<noteq> levo (roditelj q) \<and> x \<noteq> desno (roditelj q) \<and> x \<noteq> levo q \<and> x \<noteq> desno q
                             \<longrightarrow> nl!roditelj x = l!roditelj x"
    unfolding swap_def
    by auto

  from assms(1) have tv1: "\<forall>i \<in> {1..<m} - {q}. l!roditelj i \<ge> l!i"
    by auto

  (* iz podrzavajuceg uslova dobijamo da je deca u q \<le> od q -- zute grane*)
  from assms(1,2) have tv2: "najveci3roditelj l q m = roditelj q"
    by auto
  have tv2': "najveci3 nl q m = q"
  proof (cases "desno q < m")
    case True
    with tv2 have "l!roditelj q \<ge> l!levo q \<and> l!roditelj q \<ge> l!desno q"
      by (smt (verit, best) najveci3roditelj.elims)
    with swap_props(1,3) True have "nl!q \<ge> nl!levo q \<and> nl!q \<ge> nl!desno q"
      by auto
    then show ?thesis
      by auto
  next
    case False
    then show ?thesis
    proof (cases "levo q < m")
      case True
      with tv2 have "l!roditelj q \<ge> l!levo q"
        by (smt (verit, best) najveci3roditelj.elims)
      with swap_props(1,3) True have "nl!q \<ge> nl!levo q"
        by auto
      with False show ?thesis
        by auto
    next
      case False
      then show ?thesis
        by auto
    qed
  qed
  from assms(2,3) tv2' have tv2'': "(desno q < m \<and> nl!q \<ge> nl!levo q \<and> nl!q \<ge> nl!desno q) \<or> (desno q = m \<and> nl!q \<ge> nl!levo q) \<or> (desno q > m)"
    using najveci3_simp[of q m nl]
    by simp

  (* ako nije vazilo za tu jedinu granu, vazi posle swap -- siva grana *)
  from assms(4) swap_props(1,2) have tv3: "nl!roditelj q \<ge> nl!q"
    by auto

  (* ostaju iste sve grane ciji cvore ne swap-ujemo -- svetlo zelene grane *)
  have tv4: "\<forall>i \<in> {1..<m} - {roditelj q, levo (roditelj q), desno (roditelj q), levo q, desno q}. nl!roditelj i \<ge> nl!i"
  proof
    fix i
    assume at1: "i \<in> {1..<m} - {roditelj q, levo (roditelj q), desno (roditelj q), levo q, desno q}"
    with tv1 have at2: "l!roditelj i \<ge> l!i"
      by auto

    have at3: "l!roditelj i = nl!roditelj i"
      using swap_props(4) at1
      by simp

    from at1 swap_props(3) have at4: "l!i = nl!i"
      by auto

    from at2 at3 at4 show "nl!i \<le> nl!roditelj i"
      by simp
  qed

  (* grana od (roditelj q) do drugog deteta ako postoje to dete -- plava grana *)
  (* dokaz tvrdjena -- obicne grane + novi podrzavajuci uslov (narandzaste grane) *)

  from assms(2) have "q = levo (roditelj q) \<or> q =  desno (roditelj q)"
    by auto
  then show ?thesis
  proof
    assume aL: "q = levo (roditelj q)"
    from assms(3) have "q = m - 1 \<or> q < m - 1"
      by auto
    then show ?thesis
    proof 
      assume aL_bezD: "q = m - 1"

      have "roditelj q \<noteq> 0 \<longrightarrow> najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
      proof
        assume "roditelj q \<noteq> 0"
        from aL aL_bezD assms(3) have plb1: "\<not>(desno (roditelj q) < m) \<and> (levo (roditelj q) < m)"
          by auto
        with assms(2) have "roditelj q < q"
          by auto
        with \<open>roditelj q \<noteq> 0\<close> assms(3) tv1 have plb2: "l ! roditelj (roditelj q) \<ge> l ! roditelj q"
          by simp
        have "l ! roditelj (roditelj q) = nl ! roditelj (roditelj q)"
          using \<open>roditelj q \<noteq> 0\<close> assms(5) swap_props(3) swap_def
          by (smt (verit, del_insts) Suc_le_eq diff_Suc_1 diff_le_self div_less div_less_dividend less_Suc_eq_0_disj
              linorder_not_less nat_less_le nth_list_update_neq one_add_one plus_1_eq_Suc roditelj.simps)
        with swap_props(1) plb2 have "nl ! roditelj (roditelj q) \<ge> nl ! q"
          by simp
        with plb1 aL show "najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
          by simp
      qed
      then have plb_nar: "roditelj q = 0 \<or> najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
        by metis

      have "\<forall>i \<in> {1..<m} - {roditelj q, q}. nl!roditelj i \<ge> nl!i"
      proof -
        from aL_bezD have "levo q \<ge> m"
          by simp
        moreover from aL_bezD have "desno q \<ge> m"
          by simp
        moreover from aL aL_bezD have "levo (roditelj q) = q"
          by simp
        moreover from aL aL_bezD have "desno (roditelj q) = m"
          by simp
        ultimately show ?thesis
          using tv4
          by auto
      qed

      with plb_nar tv3 show ?thesis
        by auto
    next
      assume aL_saD: "q < m - 1"


      from aL aL_saD have pls5: "q + 1 < m"
        by auto
      from aL have pls6: "desno (roditelj q) = q + 1"
        by auto
      from tv1 pls5 have "l ! roditelj (q + 1) \<ge> l ! (q + 1)"
        by force
      with aL pls6 rod_desno have "l ! roditelj q \<ge> l ! (q + 1)"
        by metis
      with pls5 swap_props(1,3) have "nl ! q \<ge> nl ! (q + 1)"
        by auto
      with pls6 have pls7: "nl ! q \<ge> nl ! (desno (roditelj q))"
        by auto


      have "roditelj q \<noteq> 0 \<longrightarrow> najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
        proof
        assume "roditelj q \<noteq> 0"
        from aL aL_saD assms(3) have pls1: "desno (roditelj q) < m"
          by auto
        with assms(2) have "roditelj q < q"
          by auto
        with \<open>roditelj q \<noteq> 0\<close> assms(3) tv1 have pls2: "l ! roditelj (roditelj q) \<ge> l ! roditelj q"
          by simp
        have "l ! roditelj (roditelj q) = nl ! roditelj (roditelj q)"
          using \<open>roditelj q \<noteq> 0\<close> assms(5) swap_props(3) swap_def
          by (smt (verit, del_insts) Suc_le_eq diff_Suc_1 diff_le_self div_less div_less_dividend less_Suc_eq_0_disj
              linorder_not_less nat_less_le nth_list_update_neq one_add_one plus_1_eq_Suc roditelj.simps)
        with swap_props(1) pls2 have pls4: "nl ! roditelj (roditelj q) \<ge> nl ! q"
          by simp

        
        from pls7 pls4 have "nl ! roditelj (roditelj q) \<ge> nl ! (desno (roditelj q))"
          by simp
        with pls4 pls6 show "najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
          by simp
      qed
      then have pls_nar: "roditelj q = 0 \<or> najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
        by metis

      from pls7 tv3 have pls_plav: "nl ! desno (roditelj q) \<le> nl ! roditelj q"
        by auto

      have "\<forall>i \<in> {1..<m} - {roditelj q}.  nl ! i \<le> nl ! roditelj i"
      proof
        fix i
        assume a: "i \<in> {1..<m} - {roditelj q}"
        from tv4 have "i \<in> {1..<m} - {roditelj q, levo (roditelj q), desno (roditelj q), levo q, desno q} \<longrightarrow>  nl ! i \<le> nl ! roditelj i"
          by auto
        moreover from tv3 aL have "nl ! (levo (roditelj q)) \<le> nl ! roditelj (levo (roditelj q))"
          by auto
        moreover from pls_plav have "nl ! (desno (roditelj q)) \<le> nl ! roditelj (desno (roditelj q))"
          by auto
        moreover from tv2'' have "levo q \<ge> m \<or> nl ! (levo q) \<le> nl ! roditelj (levo q)"
          by auto
        moreover from tv2'' have "desno q \<ge> m \<or> nl ! (desno q) \<le> nl ! roditelj (desno q)"
          by auto
        ultimately have "i \<in> {1..<m} - {roditelj q} \<longrightarrow>  nl ! i \<le> nl ! roditelj i"
          by auto
        with a show "nl ! i \<le> nl ! roditelj i"
          by metis
      qed
      with pls_nar show ?thesis
        by simp
    qed
  next
    assume aD: "q = desno (roditelj q)"
    from assms(3) have pd5: "q - 1 < m"
      by auto
    from aD have pd6: "levo (roditelj q) = q - 1"
      by auto
    from assms(2) aD have pd': "q \<ge> 2"
      by auto
    with tv1 pd5 have "l ! roditelj (q - 1) \<ge> l ! (q - 1)"
      by fastforce
    with aD pd6 rod_levo have "l ! roditelj q \<ge> l ! (q - 1)"
      by metis
    with pd' pd5 swap_props(1,3) have "nl ! q \<ge> nl ! (q - 1)"
      by auto
    with pd6 have pd7: "nl ! q \<ge> nl ! (levo (roditelj q))"
      by auto


    have "roditelj q \<noteq> 0 \<longrightarrow> najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
    proof
      assume "roditelj q \<noteq> 0"
      from aD assms(3) have pd1: "levo (roditelj q) < m"
        by auto
      with assms(2) have "roditelj q < q"
        by auto
      with \<open>roditelj q \<noteq> 0\<close> assms(3) tv1 have pd2: "l ! roditelj (roditelj q) \<ge> l ! roditelj q"
        by simp
      have "l ! roditelj (roditelj q) = nl ! roditelj (roditelj q)"
        using \<open>roditelj q \<noteq> 0\<close> assms(5) swap_props(3) swap_def
        by (smt (verit, del_insts) Suc_le_eq diff_Suc_1 diff_le_self div_less div_less_dividend less_Suc_eq_0_disj
            linorder_not_less nat_less_le nth_list_update_neq one_add_one plus_1_eq_Suc roditelj.simps)
      with swap_props(1) pd2 have pd4: "nl ! roditelj (roditelj q) \<ge> nl ! q"
        by simp

        
      from pd7 pd4 have "nl ! roditelj (roditelj q) \<ge> nl ! (levo (roditelj q))"
        by simp
      with pd4 pd6 aD show "najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
        using najveci3roditelj.simps by presburger
    qed
    then have pd_nar: "roditelj q = 0 \<or> najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
      by metis

    from pd7 tv3 have pd_plav: "nl ! levo (roditelj q) \<le> nl ! roditelj q"
      by auto

    have "\<forall>i \<in> {1..<m} - {roditelj q}.  nl ! i \<le> nl ! roditelj i"
    proof
      fix i
      assume a: "i \<in> {1..<m} - {roditelj q}"
      from tv4 have "i \<in> {1..<m} - {roditelj q, levo (roditelj q), desno (roditelj q), levo q, desno q} \<longrightarrow>  nl ! i \<le> nl ! roditelj i"
        by auto
      moreover from pd_plav have "nl ! (levo (roditelj q)) \<le> nl ! roditelj (levo (roditelj q))"
        by auto
      moreover from tv3 aD have "nl ! (desno (roditelj q)) \<le> nl ! roditelj (desno (roditelj q))"
        by auto
      moreover from tv2'' have "levo q \<ge> m \<or> nl ! (levo q) \<le> nl ! roditelj (levo q)"
        by auto
      moreover from tv2'' have "desno q \<ge> m \<or> nl ! (desno q) \<le> nl ! roditelj (desno q)"
        by auto
      ultimately have "i \<in> {1..<m} - {roditelj q} \<longrightarrow>  nl ! i \<le> nl ! roditelj i"
        by auto
      with a show "nl ! i \<le> nl ! roditelj i"
        by metis
    qed
    with pd_nar show ?thesis
      by simp
  qed
qed

lemma ubaci_JesteHip1:
  assumes "SkoroHip1 l m q"
      and "q < m"
      and "q = 0 \<or> l ! roditelj q \<ge> l ! q" 
    shows "JesteHip1 l m"
  using assms
  by auto

lemma ubaci_korak_hip:
  assumes "SkoroHip1 l m q"
      and "q < m"
      and "m \<le> length l"
    shows "JesteHip1 (ubaci l q) m"
  using assms
proof (induction l q rule: ubaci.induct)
  case (1 lst i)
  show ?case
  proof (cases "i = 0 \<or> lst ! roditelj i \<ge> lst ! i")
    case True
    with 1 show ?thesis
      using ubaci_JesteHip1[of lst m i]
      by fastforce
  next
    case False
    with 1 show ?thesis
      using ubaci_SkoroHip1[of lst m i] swap_len
      by (smt (verit, best) One_nat_def Suc_pred arith_special(3) bot_nat_0.not_eq_extremum
          canonically_ordered_monoid_add_class.lessE div_less div_less_dividend lessI 
          less_add_same_cancel1 roditelj.simps trans_less_add1 ubaci.simps)
  qed    
qed

lemma ubaciSve_korak_hip:
  assumes "q < length l"
      and "JesteHip1 l q"
    shows "JesteHip1 (ubaciSve l q) (length l)"
  using assms
proof (induction l q rule: ubaciSve.induct)
  case (1 l i)
  show ?case 
  proof (cases "i \<ge> length l")
    case True
    with 1(2) show ?thesis 
      by auto
  next
    case False
    with 1 show ?thesis
      using ubaci_len ubaci_korak_hip[of l "i+1" i]
      by auto
  qed
qed

theorem ubaciSve_korektnost_hip:
  shows "JesteHip1 (ubaciSve l 0) (length l)"
  using ubaciSve_korak_hip[of 0 l]
  by auto

end