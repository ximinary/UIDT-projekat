theory HipSort
  imports Main HipSort_ubaci HipSort_izbaci
begin

fun HipSort :: "int list \<Rightarrow> int list" where
"HipSort l = izbaciSve (ubaciSve l 0) (length l)"

value "HipSort [1, 56, 7, 13, 9, 123, 76, 13, 7]"

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