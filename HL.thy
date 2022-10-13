(* Title: Hoare Logic
   Author: Georg Struth
*)

section \<open>Hoare Logic\<close>

theory HL
  imports PHL Store

begin

subsection \<open>Assignment Rules\<close>

lemma rH_assign_iff [simp]: "H\<^sub>r P (v :=\<^sub>r e) Q = (\<forall>s. P s \<longrightarrow> Q (set v e s))"
  sorry

lemma rH_assign: "H\<^sub>r (P \<circ> (set v e)) (v :=\<^sub>r e) P"
  sorry

lemma rH_assign_floyd: "H\<^sub>r P (v :=\<^sub>r e) (\<lambda>s. \<exists>w. s v = e (set v w s) \<and> P (set v w s))"
proof-
  {fix s
  assume "P s"
  hence "e s = e (fup v (s v) s) \<and> P (fup v (s v) s)"
    by simp
  hence "\<exists>w. e s = e (set v w s) \<and> P (set v w s)"
    by meson
  hence "\<exists>w. e s = e (set v w (set v e s)) \<and> P (set v w (set v e s))"
    by auto
  hence "\<exists>w. set v e s v = e (set v w (set v e s)) \<and> P (set v w (set v e s))"  
    by simp
  hence "(\<lambda>s. \<exists>w. s v = e (set v w s) \<and> P (set v w s)) (set v e s)" 
    by simp}
  thus ?thesis
    unfolding rH_assign_iff by simp
qed

abbreviation rH_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a pred \<Rightarrow> bool" ("rPRE _ _ POST _" [64,64,64] 63) where
  "rPRE P R POST Q \<equiv> H\<^sub>r P R Q"

text \<open>Next we consider state transformers.\<close>

lemma sH_assign_iff [simp]: "H\<^sub>s P (v :=\<^sub>s e) Q = (\<forall>s. P s \<longrightarrow> Q (set v e s))"
  sorry

lemma sH_assign: "H\<^sub>s (P \<circ> (set v e)) (v :=\<^sub>s e) P"
  sorry

lemma sH_assign_floyd: "H\<^sub>s P (v :=\<^sub>s e) (\<lambda>s. \<exists>w::'a store \<Rightarrow> 'a. s v = e (set v w s) \<and> P (set v w s))"
  sorry

abbreviation sH_sugar :: "'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a pred \<Rightarrow> bool" ("sPRE _ _ POST _" [64,64,64] 63) where
  "sPRE P f POST Q \<equiv> H\<^sub>s P f Q"

text \<open>The rules are set up in such a way that it should make no difference whether we work in the 
relational or the state transformer semantics. Yet this needs more testing.\<close>


subsection \<open>Examples\<close>

lemma "rPRE (\<lambda>s. True) (''q'' :=\<^sub>r (\<lambda>s. 0)) POST (\<lambda>s. s ''q'' = 0)"
  sorry

lemma "sPRE (\<lambda>s. True) (''r'' :=\<^sub>s (\<lambda>s. s ''x'')) POST (\<lambda>s. s ''r'' = s ''x'')"
  sorry

lemma "rPRE (\<lambda>s. s ''q'' = n) (''q'' :=\<^sub>r (\<lambda>s. s ''q'' + 1)) POST (\<lambda>s. s ''q'' = n + 1)"
  sorry

lemma "sPRE (\<lambda>s. s ''r'' - s y = n) (''r'' :=\<^sub>s (\<lambda>s. s ''r'' - s y)) POST (\<lambda>s. s ''r'' = n)"
  sorry

lemma "rPRE (\<lambda>s. 5 = 5) (''x'' :=\<^sub>r (\<lambda>s. 5)) POST (\<lambda>s. s ''x'' = 5)"
  sorry

lemma "sPRE (\<lambda>s. 5 = 5) (''x'' :=\<^sub>s (\<lambda>s. 5)) POST (\<lambda>s. s ''x'' = 5)"
  sorry

lemma "rPRE (\<lambda>s. s ''x'' = 1) (''x'' :=\<^sub>r (\<lambda>s. s ''x'' + 1)) POST (\<lambda>s. s ''x'' = 2)"
  sorry

lemma rvarible_swap:
  "rPRE (\<lambda>s. s ''x'' = m \<and> s ''y'' = n)   
    (''z'' :=\<^sub>r (\<lambda>s. s ''x''));
    (''x'' :=\<^sub>r (\<lambda>s. s ''y''));
    (''y'' :=\<^sub>r (\<lambda>s. s ''z''))
   POST (\<lambda>s. s ''x'' = n \<and> s ''y'' = m)"
  sorry

lemma svarible_swap:
  "sPRE (\<lambda>s. s ''x'' = m \<and> s ''y'' = n)   
    (''z'' :=\<^sub>s (\<lambda>s. s ''x'')) \<circ>\<^sub>K
    (''x'' :=\<^sub>s (\<lambda>s. s ''y'')) \<circ>\<^sub>K
    (''y'' :=\<^sub>s (\<lambda>s. s ''z''))
   POST (\<lambda>s. s ''x'' = n \<and> s ''y'' = m)"
  sorry

lemma rmaximum:  
  "rPRE (\<lambda>s::int store. True)
   (rif (\<lambda>s. s ''x'' \<ge> s ''y'') 
    then (''z'' :=\<^sub>r (\<lambda>s. s ''x''))
    else (''z'' :=\<^sub>r (\<lambda>s. s ''y''))
    fi)
   POST (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))"
  sorry

lemma smaximum: 
  "sPRE (\<lambda>s:: int store. True)
   (sif (\<lambda>s. s ''x'' \<ge> s ''y'') 
    then (''z'' :=\<^sub>s (\<lambda>s. s ''x'')) 
    else (''z'' :=\<^sub>s (\<lambda>s. s ''y''))
    fi)
   POST (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))"
  sorry

lemma rinteger_division: 
  assumes "q = ''q''" and "r = ''r''"
  shows 
  "rPRE (\<lambda>s::nat store. 0 < y)
    (q :=\<^sub>r (\<lambda>s. 0)); 
    (r :=\<^sub>r (\<lambda>s. x));
    (rwhile (\<lambda>s. y \<le> s r) inv (\<lambda>s. x = s q * y + s r \<and> 0 \<le> s r)
     do
      (q :=\<^sub>r (\<lambda>s. s q + 1));
      (r :=\<^sub>r (\<lambda>s. s r - y))
     od)
   POST (\<lambda>s. x = s q * y + s r \<and> 0 \<le> s r \<and> s r < y)"
  sorry

lemma sinteger_division: 
  assumes "q = ''q''" and "r = ''r''"
  shows 
  "sPRE (\<lambda>s::nat store. 0 < y)
    (q :=\<^sub>s (\<lambda>s. 0)) \<circ>\<^sub>K
    (r :=\<^sub>s (\<lambda>s. x)) \<circ>\<^sub>K
    (swhile (\<lambda>s. y \<le> s r) inv (\<lambda>s. x = s q * y + s r)
     do
      (q :=\<^sub>s (\<lambda>s. s q + 1)) \<circ>\<^sub>K
      (r :=\<^sub>s (\<lambda>s. s r - y))
     od)
   POST (\<lambda>s. x = s q * y + s r \<and> s r < y)"
  sorry

end



