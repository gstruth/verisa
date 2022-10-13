(* Title: Program Store
   Author: Georg Struth
*)

section \<open>Program Store\<close>

theory Store
  imports KA

begin

subsection \<open>Function update\<close>

text \<open> Isabelle provides such a function, but its type doesn't suit our needs well enough.\<close>

definition fup :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "fup x a f = (\<lambda>y. if x = y then a else f y)"

lemma fup_simp1 [simp]: "fup x a f x = a"
  sorry

lemma fup_simp2 [simp]: "x \<noteq> y \<Longrightarrow> fup x a f y = f y"
  sorry

lemma fup_absorb [simp]: "fup x a (fup x b f) = fup x a f"
  sorry

lemma fup_absorb2 [simp]: "fup x a \<circ> fup x b = fup x a"
  sorry

lemma fup_comm: "x \<noteq> y \<Longrightarrow> fup x a (fup y b f) = fup y b (fup x a f)"
  sorry

lemma fup_comm2: "x \<noteq> y \<Longrightarrow> fup x a \<circ> fup y b = fup y b \<circ> fup x a"
  sorry

lemma fup_triv [simp]: "fup x (f x) f = f"
  sorry

subsection \<open>Program Store and Semantics of Assignments\<close>

type_synonym 'a store = "string \<Rightarrow> 'a"

text \<open>We model variables as strings to have a simple kind of equality. Nevertheless, this restriction
is only needed in verification proofs; for the general set up we use arbitrary functions.\<close>

text \<open>We specialise fup to a store update function set. We could use it
below to introduce substitution notation P[v/e] for store updates of predicates, but haven't done it so far.\<close>

abbreviation set :: "'a \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "set v e s \<equiv> fup v (e s) s"
 
lemma set_pred: "P (set v e s) = (P \<circ> (set v e)) s"
  by simp

text \<open>Finally we derive the semantics of assignment rules.\<close>

definition rel_assign :: "'a \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) rel" ("_ :=\<^sub>r _" [70, 65] 61) where 
  "v :=\<^sub>r e = {(s, set v e s) |s. True}"

lemma rel_assign_iff: "((s,s') \<in> v :=\<^sub>r e) = (s' = set v e s)"
  sorry

lemma rel_assign_post_iff: "((s,s') \<in> ((v :=\<^sub>r e) ; \<lceil>Q\<rceil>\<^sub>r)) = (s' = set v e s \<and> Q s')"
  sorry

lemma rel_assign_post_dom: "(Domain ((v :=\<^sub>r e) ; \<lceil>Q\<rceil>\<^sub>r)) = {s. Q (set v e s)}"
  unfolding Domain_unfold by (simp add: rel_assign_post_iff)

definition sta_assign :: "'a \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) sta" ("_ :=\<^sub>s _" [70, 65] 61) where
  "v :=\<^sub>s e = \<eta> \<circ> (set v e)"

lemma sta_assign_eq: "(v :=\<^sub>s e) s = {set v e s}"
  sorry

lemma sta_assign_iff: "(s' \<in> (v :=\<^sub>s e) s) = (s' = set v e s)"
  sorry

end





