theory HipSort_ubaci
  imports Main HipSort_zajednicko
begin

fun ubaci :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"ubaci l i = 
   (if i = 0 \<or> l ! (roditelj i) \<ge> l ! i then 
        l 
    else
       ubaci (swap l i (roditelj i)) (roditelj i))"

function ubaciSve :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"ubaciSve l i = (if i \<ge> length l then l else ubaciSve (ubaci l i) (i+1))"
  by pat_completeness auto
termination
  sorry


fun najveci3roditelj :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"najveci3roditelj l i m = 
   (if desno i < m then
       (if l!roditelj i \<ge> l!levo i \<and> l!roditelj i \<ge> l!desno i then 
            roditelj i
        else if l!levo i \<ge> l!desno i then
            levo i
        else 
            desno i
       )
    else if levo i < m then 
        (if (l!roditelj i) \<ge> (l!levo i) then
            roditelj i
         else 
            levo i
        ) 
    else 
         roditelj i
    )"



fun JesteHip1 :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteHip1 l m = (\<forall>i \<in> {1..<m}. l ! roditelj i \<ge> l ! i)"

fun SkoroHip1 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"SkoroHip1 l m q = ((\<forall>i \<in> {1..<m} - {q}. l!roditelj i \<ge> l!i) \<and> (q = 0 \<or> najveci3roditelj l q m = roditelj q))"
                                                                         (*PODRZAVAJUCI USLOV*)

lemma VezaSkoroJeste1: "SkoroHip1 l m 0 \<longleftrightarrow> JesteHip1 l m"
  by auto



lemma ubaci_SkoroHip1:
  assumes "SkoroHip1 l m q"
      and "q \<noteq> 0"
      and "q < m" 
      and "l ! roditelj q < l ! q"
      and "nl = swap l q (roditelj q)"
      and "m \<le> length l"
    shows "SkoroHip1 nl m (roditelj q)"
proof -
  from assms(1) have tv1: "\<forall>i \<in> {1..<m} - {q}. l!roditelj i \<ge> l!i"
    by auto

  from assms(2, 3, 5, 6) have swap1: "l!roditelj q = nl!q"
    unfolding swap_def
    by auto
  from assms(2, 3, 5, 6) have swap2: "nl!roditelj q = l!q" 
    unfolding swap_def
    by auto
  from assms(5) have swap3: "\<forall>x. x < m \<and> x \<noteq> q \<and> x \<noteq> roditelj q \<longrightarrow> nl!x = l!x" 
    unfolding swap_def
    by auto
  have swap4: "\<forall>x. x < m \<and> x \<noteq> 0 \<and> x \<noteq> levo (roditelj q) \<and> x \<noteq> desno (roditelj q) \<and> x \<noteq> levo q \<and> x \<noteq> desno q
                             \<longrightarrow> nl!roditelj x = l!roditelj x" 
  proof 
    fix x
    show "x < m \<and> x \<noteq> 0 \<and> x \<noteq> levo (roditelj q) \<and> x \<noteq> desno (roditelj q) \<and> x \<noteq> levo q \<and> x \<noteq> desno q \<longrightarrow> nl ! roditelj x = l ! roditelj x"
    proof 
      assume a: "x < m \<and> x \<noteq> 0 \<and> x \<noteq> levo (roditelj q) \<and> x \<noteq> desno (roditelj q) \<and> x \<noteq> levo q \<and> x \<noteq> desno q"

      from a have a1: "x < m" by auto
      from a have a2: "x \<noteq> 0" by auto
      from a have a3: "x \<noteq> levo (roditelj q)" by auto
      from a have a4: "x \<noteq> desno (roditelj q)" by auto
      from a have a5: "x \<noteq> levo q" by auto
      from a have a6: "x \<noteq> desno q" by auto

      from assms(2) have a3': "roditelj q = roditelj (levo (roditelj q))"
        by auto
      from assms(2) have a4': "roditelj q = roditelj (desno (roditelj q))"
        by auto
      from assms(2) have a5': "q = roditelj (levo q)"
        by auto
      from assms(2) have a6': "q = roditelj (desno q)"
        by auto

      from a2 a3 a4 a3' a4' have a34: "roditelj x \<noteq> roditelj q"
        by simp

      from a2 a5 a6 a5' a6' have a56: "roditelj x \<noteq> q"
        by simp

      from a1 a2 a34 a56 show "nl ! roditelj x = l ! roditelj x"
        using swap3
        by simp
    qed
  qed
    

  (* iz podrzavajuceg uslova dobijamo da je deca u q \<le> od q -- zute grane*)
  from assms(1, 2) have tv2: "najveci3roditelj l q m = roditelj q"
    by auto
  have tv2': "najveci3 nl q m = q"
  proof (cases "desno q < m")
    case True
    with tv2 have "l!roditelj q \<ge> l!levo q \<and> l!roditelj q \<ge> l!desno q"
      by (smt (verit, best) najveci3roditelj.elims)
    with swap1 swap3 True have "nl!q \<ge> nl!levo q \<and> nl!q \<ge> nl!desno q"
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
      with swap1 swap3 True have "nl!q \<ge> nl!levo q"
        by auto
      with False show ?thesis
        by auto
    next
      case False
      then show ?thesis
        by auto
    qed
  qed
  from assms(2, 3) tv2' have tv2'': "(desno q < m \<and> nl!q \<ge> nl!levo q \<and> nl!q \<ge> nl!desno q) \<or> (desno q = m \<and> nl!q \<ge> nl!levo q) \<or> (desno q > m)"
    using l2to1slucajevi[of q m nl]
    by simp

  (* ako nije vazilo za tu jedinu granu, vazi posle swap -- siva grana *)
  from assms(4) swap1 swap2 have tv3: "nl!roditelj q \<ge> nl!q"
    by auto

  (* ostaju iste sve grane ciji cvore ne swap-ujemo -- svetlo zelene grane *)
  have tv4: "\<forall>i \<in> {1..<m} - {roditelj q, levo (roditelj q), desno (roditelj q), levo q, desno q}. nl!roditelj i \<ge> nl!i"
  proof
    fix i
    assume at1: "i \<in> {1..<m} - {roditelj q, levo (roditelj q), desno (roditelj q), levo q, desno q}"
    with tv1 have at2: "l!roditelj i \<ge> l!i"
      by auto

    have at3: "l!roditelj i = nl!roditelj i"
      using swap4 at1
      by simp

    from at1 swap3 have at4: "l!i = nl!i"
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
          using \<open>roditelj q \<noteq> 0\<close> assms(5) swap3 swap_def
          by (smt (verit, del_insts) Suc_le_eq diff_Suc_1 diff_le_self div_less div_less_dividend less_Suc_eq_0_disj
              linorder_not_less nat_less_le nth_list_update_neq one_add_one plus_1_eq_Suc roditelj.simps)
        with swap1 plb2 have "nl ! roditelj (roditelj q) \<ge> nl ! q"
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

      have podrz: "roditelj q \<noteq> 0 \<longrightarrow> najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
        sorry

      show ?thesis
        sorry
    qed
  next
    assume aD: "q = desno (roditelj q)"

    have podrz: "roditelj q \<noteq> 0 \<longrightarrow> najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
      sorry

    show ?thesis
      sorry
  qed


(*
  show "SkoroHip1 nl m (roditelj q)"
  proof (cases "roditelj q = 0")
    case True
    then have "q = 1 \<or> q = 2"
      using assms(2) mult_2 by auto
    from True tv1 tv2'' tv3 tv4  assms(4, 5) show ?thesis
      sorry
      
  next
    case False
    have "najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
      sorry


    with False tv1 swap1 swap2 assms(4, 5) show ?thesis
      sorry

  qed
*)


(*
  have "najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
  proof (cases "2 dvd q")
    case True
    have "roditelj q < m"
      using assms(3)
      by auto
    then have "roditelj q = najveci3 l (roditelj q) m"
      using tv1
  next
    case False
    then show ?thesis sorry
  qed

    

  have "najveci3 l q m = q"
  proof(cases "desno q < m")
    case True

    have hL: "l!q \<ge> l!(levo q)"
    proof -
      from True assms(3) tv1 have "l!roditelj (levo q) \<ge> l!(levo q)"
        by fastforce
      then show ?thesis
         by auto
     qed    

    have hR: "l!q \<ge> l!(desno q)"
    proof -
      from True assms(3) tv1 have "l!roditelj (desno q) \<ge> l!(desno q)"
        by fastforce
      then show ?thesis
         by auto
    qed

    from hL hR show ?thesis
      by auto
  next
    case False
    show ?thesis
    proof (cases "levo q < m")
      case True
  
      have hL: "l!q \<ge> l!(levo q)"
      proof -
        from True assms(3) tv1 have "l!roditelj (levo q) \<ge> l!(levo q)"
          by fastforce
        then show ?thesis
           by auto
       qed   
      from hL False show ?thesis
        by auto
    next
      case False
      then show ?thesis
        by auto
    qed
  qed

  with assms(4, 5) swap1 swap2 have "najveci3roditelj nl q m = roditelj q"
    unfolding swap_def
    by (smt (verit, ccfv_SIG) najveci3.simps najveci3roditelj.elims nth_list_update_neq)
*)
qed

lemma ubaci_JesteHip1:
  assumes "SkoroHip1 l m q"
      and "q < m"
      and "q = 0 \<or> l ! roditelj q \<ge> l ! q" 
    shows "JesteHip1 l m"
  using assms
  by auto

lemma ubaci_korektnost_hip:
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
    then have "JesteHip1 lst m"
      using 1(2) ubaci_JesteHip1[of lst m i]
      by auto
    then have "i = 0 \<or> lst ! roditelj i \<ge> lst ! i"
      using 1(3)
      by auto
    then have "ubaci lst i = lst"
      by auto
    then show ?thesis
      using \<open>JesteHip1 lst m\<close>
      by auto
  next
    case False
    then have p1: "SkoroHip1 (swap lst i (roditelj i)) m (roditelj i)"
      using 1(2, 3, 4) ubaci_SkoroHip1[of lst m i]
      by auto

    from 1(3) have p2: "roditelj i < m"
      by auto
    have p3: "length (swap lst i (roditelj i)) = length lst"
      by auto
    from p1 p2 p3 1(1, 4) False have p4: "JesteHip1 (ubaci (swap lst i (roditelj i)) (roditelj i)) m"
      by metis

    from False have "ubaci lst i = ubaci (swap lst i (roditelj i)) (roditelj i)"
      by auto
    with p4 show ?thesis
      by auto
  qed    
qed

lemma ubaci_len:
  assumes "i < length l"
    shows "length (ubaci l i) = length l"
  sorry

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

    from 1(3) have "SkoroHip1 l (i+1) i"
      by auto
    with False have p1: "JesteHip1 (ubaci l i) (i + 1)"
      using ubaci_korektnost_hip[of l "i+1" i]
      by auto

    show ?thesis 
      proof (cases "i + 1 \<ge> length l")
        case True
        with False have p2: "i = length l - 1"
          by auto
        with p1 show ?thesis
          by (metis p2 p1 False ubaciSve.simps ubaci_len linorder_not_less nle_le less_diff_conv less_inc_imp_less_eq)
      next
        case False
        then have "i < length (ubaci l i) - 1"
          using ubaci_len[of i l]
          by auto
        with p1 1 False have p3: "JesteHip1 (ubaciSve (ubaci l i) (i + 1)) (length (ubaci l i))"
          by linarith
        with \<open>\<not> i \<ge> length l\<close> have p4: "ubaciSve l i = ubaciSve (ubaci l i) (i+1)"
          by (meson ubaciSve.simps)
        with  p3 show ?thesis
          using ubaci_len[of i l]
          by (metis "1.prems"(1))
      qed
  qed
qed

lemma ubaciSve_korektnost_hip:
  shows "JesteHip1 (ubaciSve l 0) (length l)"
proof -
  have "JesteHip1 l 0"
    by auto
  then show "JesteHip1 (ubaciSve l 0) (length l)"
    using ubaciSve_korak_hip[of 0 l]
    by auto
qed


lemma ubaciSve_korektnost_mset:
assumes "i \<le> length l" (*?*)
shows "mset l = mset (ubaci l i)"
  unfolding swap_def
  sorry


end