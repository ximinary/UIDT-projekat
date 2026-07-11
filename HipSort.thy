theory HipSort
  imports Main HipSort_ubaci HipSort_izbaci
begin

fun HipSort :: "int list \<Rightarrow> int list" where
"HipSort l = izbaciSve (ubaciSve l 0) (length l)"

value "HipSort [1, 56, 7, 13, 9, 123, 76, 13, 7]"

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


theorem 
  shows "JesteSortiran (HipSort l) 0"
    and "mset (HipSort l) = mset l"
proof -
  have "JesteHip1 (ubaciSve l 0) (length l)"
    using ubaciSve_korektnost_hip
    by auto
  then have "JesteHip2 (ubaciSve l 0) (length l)"
    using JesteHipEkvDef
    by simp
  then have "JesteSortiran (izbaciSve (ubaciSve l 0) (length l)) 0"
    using izbaciSve_korektnost_hip[of "ubaciSve l 0"] ubaciSve_len[of l 0]
    by metis
  then show "JesteSortiran (HipSort l) 0"
    by (metis HipSort.elims)
next
  have "mset (izbaciSve (ubaciSve l 0) (length l)) = mset (ubaciSve l 0)"
    using izbaciSve_korektnost_mset[of "ubaciSve l 0"] ubaciSve_len[of l 0]
    by metis
  also have "\<dots> = mset l"
    using ubaciSve_korektnost_mset
    by simp
  finally show "mset (HipSort l) = mset l"
    by simp
qed

end