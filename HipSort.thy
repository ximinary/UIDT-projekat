theory HipSort
  imports Main HipSort_ubaci HipSort_izbaci
begin

fun HipSort :: "int list \<Rightarrow> int list" where
"HipSort l = izbaciSve (ubaciSve l 0) (length l)"


lemma JesteHipEkvDef: "JesteHip1 l m = JesteHip2 l m"
proof
  assume "JesteHip1 l m"
  then have *: "\<forall>i. (0 < i \<and> i < m) \<longrightarrow> l!(roditelj i) \<ge> l!i"
    by auto
  have "\<forall>i. i < m \<longrightarrow> i = najveci3 l i m"
  proof 
    fix i::nat

    show "i < m \<longrightarrow> i = najveci3 l i m "
      using * l1to2
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
      using l2to1 *
      by auto
  qed
  then show "JesteHip1 l m"
    by auto
qed


theorem 
  shows "sorted (HipSort l)"
    and "mset (HipSort l) = mset l"
proof -
  have "JesteHip1 (ubaciSve l 0) (length l)"
    using ubaciSve_korektnost_hip
    by simp
  then have "JesteHip2 (ubaciSve l 0) (length l)"
    using JesteHipEkvDef
    by simp
  then show "sorted (HipSort l)"
    sorry (*izbaci teo_sort*)

next
  have "mset (ubaciSve l 0) = mset l"
    using ubaciSve_korektnost_mset
    by simp
  then show "mset (HipSort l) = mset l"
    sorry (*izbaci teo_mset*)

qed

end