theory HipSort_izbaci
  imports Main HipSort_zajednicko
begin

function izbaci :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list" where
"izbaci l i m = (let najveci = najveci3 l i m in 
    (if i = najveci then l
         else izbaci (swap l i najveci) najveci m))"
  by pat_completeness auto
termination
  sorry

fun izbaciSve :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"izbaciSve l i = (if i = 0 then l else izbaciSve (izbaci (swap l 0 (i-1)) 0 (i-1)) (i-1))"



fun JesteHip2 :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteHip2 l m = (\<forall>i \<in> {0..<m}. i = najveci3 l i m)"

fun SkoroHip2 :: "int list \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> bool" where
"SkoroHip2 l m q = (\<forall>i \<in> {0..<m} - {q}. i = najveci3 l i m)"

lemma VezaSkoroJeste2: "2*q + 1 > m \<and> SkoroHip2 l m q \<longrightarrow> JesteHip2 l m"
proof
  assume *: "m < 2 * q + 1 \<and> SkoroHip2 l m q"
  from * have "\<forall>i \<in> {0..<m} - {q}. i = najveci3 l i m"
    by auto
  moreover
  from * have "q = najveci3 l q m"
    by auto
  ultimately show "JesteHip2 l m"
    by (metis JesteHip2.elims(3) insert_iff insert_Diff_single)
qed

fun JesteSortiran :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteSortiran l m = sorted (drop m l)"




lemma izbaciSve_inv1:
assumes "0 < i \<and> i \<le> length l" (*?*)
and "JesteHip l i"
and "JesteSortiran l i"
and "l ! 0 \<le> l ! i"
and "nl = (swap l 0 (i-1))"

shows "JesteHip (izbaci nl 0 (i-1)) (i-1)" 
and "JesteSortiran (izbaci nl 0 (i-1)) (i-1)"
and "nl ! 0 \<le> nl ! (i-1)"
  sorry

lemma izbaciSve_korektnost_mset:
assumes "0 < i \<and> i \<le> length l" (*?*)
shows "mset l = mset (izbaci (swap l 0 (i-1)) 0 (i-1))"
  unfolding swap_def 
  sorry


end