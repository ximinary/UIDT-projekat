theory zbirSegmenta
  imports Main "HOL-Library.Sublist"
begin

function NajveciZbirSegmenta' :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"NajveciZbirSegmenta' l i tr mx = 
                      (if (i \<ge> length l)
                          then mx
                          else
                              (let ntr = max 0 (tr + (l ! i)) in
                                  NajveciZbirSegmenta' l (i+1) ntr (max ntr mx)
                      ))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(l, i, tr, mx). (length l - i))") auto

fun NajveciZbirSegmenta :: "int list \<Rightarrow> int" where
  "NajveciZbirSegmenta l = NajveciZbirSegmenta' l 0 0 0"

fun NajveciZbirSegmentaGS :: "int list \<Rightarrow> int" where
"NajveciZbirSegmentaGS l = Max (set (map sum_list (sublists l)))"

fun NajveciPoslednjiZbirSegmentaGS :: "int list \<Rightarrow> int" where
"NajveciPoslednjiZbirSegmentaGS l = Max (set (map sum_list (suffixes l)))"

lemma maximum_map_plus:
  fixes n::int
  assumes "s \<noteq> {}"
  and "finite s"
  shows "Max ((\<lambda> s. s + n) ` s) = Max s + n"
  by (smt (verit, best) assms(1,2) hom_Max_commute max_def)


lemma max_nsuffixes:
  fixes n::int
  shows "Max (set (map sum_list (suffixes (lst @ [n])))) 
         = max 0 (Max (set (map sum_list (suffixes lst))) + n)"
proof -
   have "Max (set (map sum_list (suffixes (lst @ [n]))))
                = Max (set (map sum_list ([] # map (\<lambda> xs. xs @ [n]) (suffixes lst))))"
    by auto
  also have "\<dots> = max 0 (Max (set (map sum_list (map (\<lambda> xs. xs @ [n]) (suffixes lst)))))"
    by auto
  also have "\<dots> = max 0 (Max (set (map (sum_list \<circ> (\<lambda> xs. xs @ [n]))  (suffixes lst))))"
    by auto
  also have "\<dots> = max 0 (Max (set (map ((\<lambda> s. s + n) \<circ> sum_list) (suffixes lst))))"
    by auto
  also have "\<dots> = max 0 (Max (set (map (\<lambda> s. s + n) (map sum_list (suffixes lst)))))"
    by auto
  also have "\<dots> = max 0 (Max ((\<lambda> s. s + n) ` set (map sum_list (suffixes lst))))"
    by (metis list.set_map)
  also have "\<dots> = max 0 (Max (set (map sum_list (suffixes lst))) + n)"
    using maximum_map_plus[of "set (map sum_list (suffixes lst))" n]
    by auto
  finally show ?thesis
    .
qed


lemma nsublists: "(set (sublists (lst @ [n]))) = (set (sublists lst) \<union> set (suffixes (lst @ [n])))"
  by (induct lst) auto

lemma maximum_union:
  fixes n::int
  assumes "s1 \<noteq> {}" 
  and "s2 \<noteq> {}"
  and "finite s1"
  and "finite s2"
  shows "Max (s1 \<union> s2) = max (Max s1) (Max s2)"
  using assms Max.union
  by blast

lemma max_nsublists:
  fixes n::int
  shows "Max (set (map sum_list (sublists (lst @ [n])))) 
         = max (Max (set (map sum_list (sublists lst)))) 
               (max 0 (Max (set (map sum_list (suffixes lst))) + n))"
proof -
  have "Max (set (map sum_list (sublists (lst @ [n])))) 
                = Max (sum_list ` set (sublists (lst @ [n])))"
    by auto
  also have "\<dots> = Max (sum_list ` (set (sublists lst) \<union> set (suffixes (lst @ [n]))))"
    by (auto simp add: nsublists)
  also have "\<dots> = Max (sum_list ` set (sublists lst) \<union> (sum_list ` set (suffixes (lst @ [n]))))"
    by (auto simp add: image_Un)
  also have "\<dots> = max (Max (sum_list ` set (sublists lst))) (Max (sum_list ` set (suffixes (lst @ [n]))))"
    using maximum_union[of "sum_list ` set (sublists lst)" "sum_list ` set (suffixes (lst @ [n]))"]
    by (metis empty_iff in_set_sublists list.distinct(1) list.map_disc_iff list.set_finite list.set_map set_empty
        sublist_Nil_left suffixes_snoc)
  also have "\<dots> = max (Max (set (map sum_list (sublists lst)))) (Max (sum_list ` set (suffixes (lst @ [n]))))"
    by auto
  also have "\<dots> = max (Max (set (map sum_list (sublists lst)))) (Max (set (map sum_list (suffixes (lst @ [n])))))"
    by (metis list.set_map)
  also have "\<dots> = max (Max (set (map sum_list (sublists lst)))) (max 0 (Max (set (map sum_list (suffixes lst))) + n))"
    using max_nsuffixes[of lst n]
    by auto

  finally show ?thesis
    .
qed

lemma novi_el:
  assumes "i < length l" 
  shows "(take (i + 1) l) = (take i l) @ [l ! i]"  
    using assms take_Suc_conv_app_nth
    by auto

lemma NZS_iteracija:
  assumes "i < length l"

      and "tr = NajveciPoslednjiZbirSegmentaGS (take i l)"
      and "mx = NajveciZbirSegmentaGS (take i l)"
      
      and "ntr = max 0 (tr + (l ! i))"
      and "nmx = max ntr mx"

    shows "NajveciPoslednjiZbirSegmentaGS (take (i+1) l) = ntr" 
      and "NajveciZbirSegmentaGS (take (i+1) l) = nmx"
proof -
  let ?nlst = "take (i + 1) l"
  let ?lst  = "take       i l"
  let ?n    = "l ! i"

  have "NajveciPoslednjiZbirSegmentaGS ?nlst = NajveciPoslednjiZbirSegmentaGS (?lst @ [?n])"
    using assms(1) novi_el[of i l]
    by auto
  also have "\<dots> = Max (set (map sum_list (suffixes (?lst @ [?n]))))"
    by auto
  also have "\<dots> = max 0 (Max (set (map sum_list (suffixes ?lst))) + ?n)"
    using max_nsuffixes[of ?lst ?n]
    by auto
  also have "\<dots> = max 0 (NajveciPoslednjiZbirSegmentaGS ?lst + ?n)"
    by auto
  finally show ntr_goal: "NajveciPoslednjiZbirSegmentaGS (take (i+1) l) = ntr"
    using assms
    by auto

next

  let ?nlst = "take (i + 1) l"
  let ?lst  = "take       i l"
  let ?n    = "l ! i"

  have "NajveciZbirSegmentaGS ?nlst = NajveciZbirSegmentaGS (?lst @ [?n])"
    using assms(1) novi_el[of i l]
    by auto
  also have "\<dots> = Max (set (map sum_list (sublists (?lst @ [?n]))))"
    by auto
  also have "\<dots> = max (Max (set (map sum_list (sublists ?lst)))) (max 0 (Max (set (map sum_list (suffixes ?lst))) + ?n))"
    using max_nsublists[of ?lst ?n]
    by auto
  also have "\<dots> = max mx ntr"
    using assms
    by auto 
  finally show nmx_goal: "NajveciZbirSegmentaGS (take (i+1) l) = nmx"
    using assms
    by auto
qed


fun invarianta :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"invarianta l i tr mx = ((NajveciPoslednjiZbirSegmentaGS (take i l) = tr) 
                       \<and> (NajveciZbirSegmentaGS (take i l) = mx))"

lemma NajveciZbirSegmenta'_korak:
  assumes "invarianta l i tr mx"
  shows "NajveciZbirSegmenta' l i tr mx = NajveciZbirSegmentaGS l"
  using assms
proof (induct l i tr mx rule: NajveciZbirSegmenta'.induct)
  case (1 l i tr mx)
  then show ?case 
    using NZS_iteracija[of i l tr mx]
    by auto
qed

theorem NajveciZbirSegmenta_korektnost:
  shows "NajveciZbirSegmenta l = NajveciZbirSegmentaGS l"
  using NajveciZbirSegmenta'_korak[of l 0 0 0]
  by auto

end
