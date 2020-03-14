(* Title: Program Store
   Author: Georg Struth
*)

section \<open>Program Store\<close>

theory Store
  imports KA

begin

subsection \<open>Function update\<close>

text \<open> Isabelle provides such a function, but its type doesn't suit our needs well enough.\<close>

definition fup :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" ("\<Delta>") where
  "\<Delta> x a f = (\<lambda>y. if x = y then a else f y)"

lemma fun_update_simp1 [simp]: "\<Delta> x a f x = a"
  sorry

lemma fun_update_simp2 [simp]: "x \<noteq> y \<Longrightarrow> \<Delta> x a f y = f y"
  sorry

lemma fun_update_absorb [simp]: "\<Delta> x a (\<Delta> x b f) = \<Delta> x a f"
  sorry

lemma fun_update_absorb2 [simp]: "\<Delta> x a \<circ> \<Delta> x b = \<Delta> x a"
  sorry

lemma fun_update_comm: "x \<noteq> y \<Longrightarrow> \<Delta> x a (\<Delta> y b f) = \<Delta> y b (\<Delta> x a f)"
  sorry

lemma fun_update_comm2: "x \<noteq> y \<Longrightarrow> \<Delta> x a \<circ> \<Delta> y b = \<Delta> y b \<circ> \<Delta> x a"
  sorry

lemma fun_update_triv [simp]: "\<Delta> x (f x) f = f"
  sorry

abbreviation set :: "'a \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "set x e s \<equiv> \<Delta> x (e s) s"


subsection \<open>Program Store and Semantics of Assignments\<close>

type_synonym 'a store = "string \<Rightarrow> 'a"

definition rel_assign :: "'a \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) rel" ("_ :=\<^sub>r _" [70, 65] 61) where 
  "v :=\<^sub>r e = {(s, set v e s) |s. True}"

lemma rel_assign_iff: "((s,s') \<in> v :=\<^sub>r e) = (s' = set v e s)"
  by (simp add: rel_assign_def)

definition sta_assign :: "'a \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) sta" ("_ :=\<^sub>s _" [70, 65] 61) where
  "v :=\<^sub>s e = \<eta> \<circ> set v e"

lemma sta_assign_eq: "(v :=\<^sub>s e) s = {set v e s}"
  sorry


lemma sta_assign_iff: "(s' \<in> (v :=\<^sub>s e) s) = (s' = set v e s)"
  sorry

end



