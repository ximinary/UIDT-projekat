theory HipSort_zajednicko
  imports Main "HOL-Library.Discrete_Functions" "HOL-Library.Multiset"
begin

definition swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "swap l i j = l[i := l ! j, j := l ! i]"

fun roditelj :: "nat \<Rightarrow> nat" where
  "roditelj i = (i - 1) div 2"

fun levo :: "nat \<Rightarrow> nat" where
  "levo i = 2*i + 1"

fun desno :: "nat \<Rightarrow> nat" where
  "desno i = 2*i + 2"

fun dubina :: "nat \<Rightarrow> nat" where
  "dubina i = floor_log (i+1)"

lemma mset_swap[simp]: 
assumes "i < length l"
and "j < length l"
shows "mset (swap l i j) = mset l"
  using assms
  unfolding swap_def
  by (metis assms(2) assms(1) mset_swap)

lemma swap_len[simp]:
shows "length (swap l i j) = length l"
  unfolding swap_def
  by (metis length_list_update)

(*
lemma swap_lemma1:
  assumes "i < length l"
  and "j < length l"
  shows "\<forall>k \<in> {0..<length l} - {i, j}. l!k = (swap l i j)!k"
  unfolding swap_def
  by auto

lemma swap_lemma2:
  assumes "i < length l"
  and "j < length l"
  shows "(swap l i j)!i = l!j"
  and "(swap l i j)!j = l!i" 
  unfolding swap_def
  using assms
  sledgehammer
  by (metis list_update_id nth_list_update_eq nth_list_update_neq, simp)
*)


fun najveci3 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"najveci3 l i m = 
   (if desno i < m then
       (if l!i >= l!levo i \<and> l!i >= l!desno i then 
            i
        else if l!levo i >= l!desno i then
            levo i
        else 
            desno i
       )
    else if levo i < m then 
        (if (l!i) \<ge> (l!levo i) then
            i 
         else 
            levo i
        ) 
    else 
         i
    )"




lemma l2to1:
  assumes "0 < i"
  and "i < m"
  and "najveci3 l (roditelj i) m = roditelj i"
  shows " l ! roditelj i \<ge> l ! i"
proof (cases "2 dvd i")
  case True
  have "roditelj i < m"
      using assms
      by (metis One_nat_def Suc_leI True add_Suc_right diff_le_self div_less_dividend lessI nat_arith.rule0
          nat_dvd_not_less nat_less_le one_add_one order_less_le_trans roditelj.simps zero_less_diff)
    then have "roditelj i = najveci3 l (roditelj i) m"
      using assms
      by auto
    moreover
    have "i = desno (roditelj i)"
      using assms True
      by (metis One_nat_def Suc_pred add.commute add_gr_0 desno.elims div2_Suc_Suc dvdE even_Suc_div_two lessI
          mult_Suc_right nat_less_le nonzero_mult_div_cancel_left one_add_one roditelj.simps)
    ultimately show ?thesis
      by (smt (verit, ccfv_SIG) assms najveci3.simps)
next
  case False
  have "roditelj i < m"
    using assms
    by (metis (no_types, lifting) One_nat_def Suc_le_eq Suc_pred add_Suc_right div_less div_less_dividend
        linorder_not_less nat_arith.rule0 nat_less_le one_add_one order_less_le_trans roditelj.simps)
  then have "roditelj i = najveci3 l (roditelj i) m"
    using assms
    by metis
  moreover
  have "i = levo (roditelj i)"
    using assms False
    by auto
  ultimately show ?thesis
    by (smt (verit, ccfv_SIG) assms najveci3.simps)
qed

lemma l2to1slucajevi:
  assumes "0 < i"
  and "i < m"
  and  "najveci3 l i m = i"
  shows "(desno i < m \<and> l!i \<ge> l!levo i \<and> l!i \<ge> l!desno i) \<or> (desno i = m \<and> l!i \<ge> l!levo i) \<or> (desno i > m)"
  using assms
  by (smt (verit, del_insts) One_nat_def add_Suc_right desno.elims lessI levo.elims linorder_less_linear najveci3.simps
      nat_arith.rule0 one_add_one)

lemma slucajevi:
  shows "desno i < m \<or> desno i = m \<or> desno i > m"
  by auto

lemma najveci3slucaj1:
  assumes "desno i < m"
  shows "(najveci3 l i m = i) \<longleftrightarrow> (l!i \<ge> l!levo i \<and> l!i \<ge> l!desno i)"
  using assms
  by auto

lemma najveci3slucaj2:
  assumes "desno i = m"
  shows "(najveci3 l i m = i) \<longleftrightarrow> (l!i \<ge> l!levo i)"
  using assms
  by auto

lemma najveci3slucaj3:
  assumes "desno i > m"
  shows "najveci3 l i m = i"
  using assms
  by auto

lemma l1to2:
  assumes "(desno i < m \<and> l!i \<ge> l!levo i \<and> l!i \<ge> l!desno i) \<or> (desno i = m \<and> l!i \<ge> l!levo i) \<or> (desno i > m)"
  shows "najveci3 l i m = i"
  using assms
  by auto

end