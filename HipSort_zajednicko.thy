theory HipSort_zajednicko
  imports Main "HOL-Library.Multiset"
begin

definition swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
"swap l i j = l[i := l ! j, j := l ! i]"

fun roditelj :: "nat \<Rightarrow> nat" where
"roditelj i = (i - 1) div 2"

fun levo :: "nat \<Rightarrow> nat" where
"levo i = 2*i + 1"

fun desno :: "nat \<Rightarrow> nat" where
"desno i = 2*i + 2"

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

lemma swap_step_by_step:
  "swap l i j = (let x = l ! i in
                  (l[i := l ! j])[j := x])"
  using swap_def
  by auto

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

fun JesteHip1 :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteHip1 l m = (\<forall>i \<in> {1..<m}. l ! roditelj i \<ge> l ! i)"

fun JesteHip2 :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteHip2 l m = (\<forall>i \<in> {0..<m}. najveci3 l i m = i)"


lemma roditelj_je_najveci3:
  assumes "0 < i"
      and "i < m"
      and "najveci3 l (roditelj i) m = roditelj i"
    shows "l ! roditelj i \<ge> l ! i"
  using assms desno_rod_even levo_rod_odd
  by (smt (verit, best) najveci3.simps nat_less_le)

lemma JesteHipEkvDef: "JesteHip1 l m = JesteHip2 l m"
proof
  assume "JesteHip1 l m"
  then have *: "\<forall>i. (0 < i \<and> i < m) \<longrightarrow> l!(roditelj i) \<ge> l!i"
    by auto
  have "\<forall>i. i < m \<longrightarrow> i = najveci3 l i m"
  proof 
    fix i::nat
    show "i < m \<longrightarrow> i = najveci3 l i m "
      using *
      by auto
  qed
  then show "JesteHip2 l m"
    by auto
next
  assume "JesteHip2 l m"
  then have *: "\<forall>i. i < m \<longrightarrow> i = najveci3 l i m"
    by auto
  have "\<forall>i. (0 < i \<and> i < m) \<longrightarrow> l!(roditelj i) \<ge> l!i"
  proof
    fix i::nat
    show "0 < i \<and> i < m \<longrightarrow> l ! i \<le> l ! roditelj i"
      using roditelj_je_najveci3 *
      by auto
  qed
  then show "JesteHip1 l m"
    by auto
qed

end