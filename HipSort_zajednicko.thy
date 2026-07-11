theory HipSort_zajednicko
  imports Main (*"HOL-Library.Discrete_Functions"*) "HOL-Library.Multiset"
begin

definition swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "swap l i j = l[i := l ! j, j := l ! i]"

fun roditelj :: "nat \<Rightarrow> nat" where
  "roditelj i = (i - 1) div 2"

fun levo :: "nat \<Rightarrow> nat" where
  "levo i = 2*i + 1"

fun desno :: "nat \<Rightarrow> nat" where
  "desno i = 2*i + 2"

(*
fun dubina :: "nat \<Rightarrow> nat" where
  "dubina i = floor_log (i+1)"
*)

lemma rod_levo:
  shows "roditelj (levo  q) = q"
  by simp

lemma rod_desno:
  shows "roditelj (desno q) = q"
  by simp

lemma levo_rod_odd:
  assumes "\<not> (2 dvd q)" 
    shows "levo (roditelj q) = q"      
  using assms by simp

lemma levo_rod_even:
  assumes "q \<noteq> 0"
      and "2 dvd q"
    shows "levo (roditelj q) = q - 1" 
  using assms by auto

lemma desno_rod_odd:
  assumes "\<not> (2 dvd q)"
    shows "desno (roditelj q) = q + 1"
  using assms by simp

lemma desno_rod_even:
  assumes "q \<noteq> 0"
      and "2 dvd q"
    shows "desno (roditelj q) = q"
  using assms by auto


lemma swap_len:
  shows "length (swap l i j) = length l"
  unfolding swap_def
  by (metis length_list_update)

lemma swap_mset: 
  assumes "i < length l"
      and "j < length l"
    shows "mset (swap l i j) = mset l"
  using assms
  unfolding swap_def
  by (metis assms(2) assms(1) mset_swap)


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

lemma najveci3_simp:
  assumes "i < m"
      and  "najveci3 l i m = i"
    shows "(desno i < m \<and> l!i \<ge> l!levo i \<and> l!i \<ge> l!desno i) \<or> (desno i = m \<and> l!i \<ge> l!levo i) \<or> (desno i > m)"
  using assms
  by (smt (verit, best) One_nat_def add_less_cancel_left desno.simps lessI levo.simps linorder_less_linear
      najveci3.simps numeral_2_eq_2)

lemma najveci3roditelj_simp:
  assumes "0 < i" 
      and "i < m"
      and  "najveci3roditelj l i m = i"
    shows "(desno i < m \<and> l!roditelj i \<ge> l!levo i \<and> l!roditelj i \<ge> l!desno i) \<or> (desno i = m \<and> l!roditelj i \<ge> l!levo i) \<or> (desno i > m)"
  using assms desno_rod_even levo_rod_odd rod_desno rod_levo
  by (smt (verit, best) linorder_less_linear najveci3roditelj.elims nat_less_le)


lemma roditelj_je_najveci3:
  assumes "0 < i"
      and "i < m"
      and "najveci3 l (roditelj i) m = roditelj i"
    shows "l ! roditelj i \<ge> l ! i"
  using assms desno_rod_even levo_rod_odd
  by (smt (verit, best) najveci3.simps nat_less_le)

end