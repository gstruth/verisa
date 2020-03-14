(* Title: Kleene Algebra with Tests
   Author: Georg Struth
*)

section \<open>Kleene Algebra with Tests\<close>

theory KAT
  imports KA

begin

subsection \<open>Definitions and Basic Properties\<close>

class kat = kleene_algebra +
  fixes atest :: "'a \<Rightarrow> 'a" ("\<alpha>")
  assumes test_one [simp]: "\<alpha> (\<alpha> 1) = 1"
  and test_mult [simp]: "\<alpha> (\<alpha> (\<alpha> (\<alpha> x) \<cdot> \<alpha> (\<alpha> y))) = \<alpha> (\<alpha> y) \<cdot> \<alpha> (\<alpha> x)" 
  and test_mult_comp [simp]: "\<alpha> x \<cdot> \<alpha> (\<alpha> x) = 0"
  and test_de_morgan: "\<alpha> (\<alpha> (\<alpha> x) \<cdot> \<alpha> (\<alpha> y)) = \<alpha> x + \<alpha> y"

begin

definition test :: "'a \<Rightarrow> 'a"  ("\<tau>") where
  "\<tau> x = \<alpha> (\<alpha> x)"

lemma a_a [simp]: "\<alpha> \<circ> \<alpha> = \<tau>"
  sorry

lemma t_a [simp]: "\<tau> \<circ> \<alpha> = \<alpha>"
  sorry

lemma t_a_var [simp]: "\<tau> (\<alpha> x) = \<alpha> x"
  sorry

lemma a_t [simp]: "\<alpha> \<circ> \<tau> = \<alpha>"
  sorry

lemma a_t_var [simp]: "\<alpha> (\<tau> x) = \<alpha> x"
  sorry

lemma t_t [simp]: "\<tau> \<circ> \<tau> = \<tau>"
  sorry

lemma t_t_var [simp]: "\<tau> (\<tau> x) = \<tau> x"
  sorry

lemma a_comm: "\<alpha> x \<cdot> \<alpha> y = \<alpha> y \<cdot> \<alpha> x"
  sorry
 
lemma a_idem [simp]: "\<alpha> x \<cdot> \<alpha> x = \<alpha> x"
  sorry

lemma t_add_closed [simp]: "\<tau> (\<alpha> x + \<alpha> y) = \<alpha> x + \<alpha> y"
  sorry

lemma t_mult_closed [simp]: "\<tau> (\<alpha> x \<cdot> \<alpha> y) = \<alpha> x \<cdot> \<alpha> y"
  sorry

lemma t_at_compl1 [simp]: "\<tau> x + \<alpha> x = 1"
  sorry

lemma t_at_compl2 [simp]: "\<tau> x \<cdot> \<alpha> x = 0"
  sorry

lemma a_absorb1 [simp]: "\<alpha> x \<cdot> (\<alpha> x + \<alpha> y) = \<alpha> x"
  sorry

lemma a_absorb2 [simp]: "\<alpha> x + \<alpha> x \<cdot> \<alpha> y = \<alpha> x"
  sorry

lemma t_distl2: "\<alpha> x + \<alpha> y \<cdot> \<alpha> z = (\<alpha> x + \<alpha> y) \<cdot> (\<alpha> x + \<alpha> z)"
  sorry

lemma a_de_morgan2: "\<alpha> (\<alpha> x + \<alpha> y) = \<tau> x \<cdot> \<tau> y"
  sorry

lemma a_de_morgan3: "\<alpha> (\<alpha> x \<cdot> \<alpha> y) = \<tau> x + \<tau> y"
  sorry

lemma a_lbl: "\<alpha> x \<cdot> \<alpha> y \<le> \<alpha> x"
  sorry

lemma a_lbr: "\<alpha> x \<cdot> \<alpha> y \<le> \<alpha> y"
  sorry

lemma a_upper: "\<alpha> z \<le> \<alpha> x \<Longrightarrow> \<alpha> z \<le> \<alpha> y \<Longrightarrow> \<alpha> z \<le> \<alpha> x \<cdot> \<alpha> y"
  sorry

lemma a_glb: "(\<tau> z \<le> \<tau> x \<cdot> \<tau> y) = (\<tau> z \<le> \<tau> x \<and> \<tau> z \<le> \<tau> y)"
  sorry

lemma t_subid: "\<tau> x \<le> 1"
  sorry

lemma a_subid: "\<alpha> x \<le> 1"
  sorry

lemma a_comp_ord_def: "(\<alpha> x \<le> \<alpha> y) = (\<alpha> x \<cdot> \<alpha> y = \<alpha> x)"
  sorry

lemma t_le_antitone: "(\<tau> x \<le> \<tau> y) = (\<alpha> y \<le> \<alpha> x)"
  sorry

lemma at_shunt: "(\<alpha> x \<cdot> \<alpha> y \<le> \<alpha> z) = (\<alpha> x \<le> \<tau> y + \<alpha> z)"
  sorry

end

subsection \<open>Boolean Subalgebra of Tests\<close>

typedef (overloaded) 'a test_alg = "{x::'a::kat. \<tau> x = x}"
  by (meson CollectI t_a_var)

setup_lifting type_definition_test_alg

instantiation test_alg :: (kat) boolean_algebra
begin

lift_definition minus_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> 'a test_alg" is "\<lambda>x y. x \<cdot> \<alpha> y"
  by (metis t_mult_closed test_def)

lift_definition uminus_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg" is "\<alpha>"
  by simp

lift_definition bot_test_alg :: "'a test_alg" is "0"
  by (metis t_mult_closed test_mult_comp)

lift_definition top_test_alg :: "'a test_alg" is "1"
  by (simp add: test_def)

lift_definition inf_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> 'a test_alg" is "(\<cdot>)"
  by (metis t_mult_closed test_def)

lift_definition sup_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> 'a test_alg" is "(+)"
  by (metis t_add_closed test_def)

lift_definition less_eq_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> bool" is "(\<le>)".

lift_definition less_test_alg :: "'a test_alg \<Rightarrow> 'a test_alg \<Rightarrow> bool" is "(<)".

instance
  sorry

end


text \<open>Unfortunately, this theorem must be given outside of the context of the Kleene algebra with tests class.
We can therefore not use its results within this context. This means in particular that theorems from
Isabelle's boolean algebra component are not within scope within this context.\<close>

subsection \<open>Properties Helpful for Propositional Hoare Logic\<close>

context kat
begin

lemma pcorrect_if1: "\<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q \<Longrightarrow> \<alpha> p \<cdot> x \<cdot> \<tau> q = 0"
  sorry

lemma pcorrect_if1_op: "x \<cdot> \<alpha> q \<le> \<alpha> p \<cdot> x \<Longrightarrow> \<tau> p \<cdot> x \<cdot> \<alpha> q = 0"
  sorry

lemma pcorrect_if2: "\<alpha> p \<cdot> x \<cdot> \<tau> q = 0 \<Longrightarrow> \<alpha> p \<cdot> x \<cdot> \<alpha> q = \<alpha> p \<cdot> x" 
  sorry

lemma pcorrect_if2_op: "\<tau> p \<cdot> x \<cdot> \<alpha> q = 0 \<Longrightarrow> \<alpha> p \<cdot> x \<cdot> \<alpha> q = x \<cdot> \<alpha> q" 
  sorry

lemma pcorrect_if3: "\<alpha> p \<cdot> x = \<alpha> p \<cdot> x \<cdot> \<alpha> q \<Longrightarrow> \<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q"
  sorry

lemma pcorrect_if3_op: "\<alpha> p \<cdot> x \<cdot> \<alpha> q = x \<cdot> \<alpha> q \<Longrightarrow> x \<cdot> \<alpha> q \<le> \<alpha> p \<cdot>  x"
  sorry

lemma pcorrect_iff1: "(\<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q) = (\<alpha> p \<cdot> x \<cdot> \<tau> q = 0)"  
  sorry

lemma pcorrect_iff1_op: "(x \<cdot> \<alpha> q \<le> \<alpha> p \<cdot> x) = (\<tau> p \<cdot> x \<cdot> \<alpha> q = 0)"  
  sorry

lemma pcorrect_iff2: "(\<alpha> p \<cdot> x \<cdot> \<tau> q = 0) = (\<alpha> p \<cdot> x \<cdot> \<alpha> q = \<alpha> p \<cdot> x)" 
  sorry

lemma pcorrect_iff2_op: "(\<tau> p \<cdot> x \<cdot> \<alpha> q = 0) = (\<alpha> p \<cdot> x \<cdot> \<alpha> q  = x \<cdot> \<alpha> q)" 
  sorry

lemma pcorrect_op: "(\<alpha> p \<cdot> x \<le> x \<cdot> \<alpha> q) = (x \<cdot> \<tau> q \<le> \<tau> p \<cdot> x)"
  sorry

subsection  \<open>Conditionals and while-Loops.\<close>

definition cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi = \<tau> p \<cdot> x + \<alpha> p \<cdot> y"

definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while p do x od = (\<tau> p \<cdot> x)\<^sup>\<star> \<cdot> \<alpha> p"


subsection \<open>Program Equivalences and Transformations\<close>

lemma while_rec: "while p do x od = if p then x \<cdot> (while p do x od) else 1 fi"
  sorry

lemma cond_merge_aux: "(\<tau> p \<cdot> x = x \<cdot> \<tau> p) = (\<alpha> p \<cdot> x = x \<cdot> \<alpha> p)"
  sorry

lemma cond_merge:
  assumes "\<tau> p \<cdot> x = x \<cdot> \<tau> p"
  shows "if p then (x \<cdot> y) else (x \<cdot> z) fi = x \<cdot> (if p then y else z fi)"
  sorry

lemma loop_denest: "while p do (x \<cdot> (while q do y od)) od = if p then (x \<cdot> (while (\<tau> p + \<tau> q) do (if q then y else x fi) od)) else 1 fi"
  sorry

end

subsection \<open>A Locale for KAT\<close>

locale katloc =
  fixes test :: "'a::boolean_algebra \<Rightarrow> 'b::kleene_algebra" ("\<iota>")
  and not :: "'b::kleene_algebra \<Rightarrow> 'b::kleene_algebra" ("!")
  assumes test_sup: "\<iota> (sup p q) = \<iota> p + \<iota> q"
  and test_inf: "\<iota> (inf p q) = \<iota> p \<cdot> \<iota> q"
  and test_top: "\<iota> top = 1"
  and test_bot: "\<iota> bot = 0"
  and test_not: "\<iota> (- p) = ! (\<iota> p)" 
  and test_iso_eq: "p \<le> q \<longleftrightarrow> \<iota> p \<le> \<iota> q"

begin

lemma test_eq: "p = q \<longleftrightarrow> \<iota> p = \<iota> q"
  by (metis eq_iff test_iso_eq)

lemma test_iso: "p \<le> q \<Longrightarrow> \<iota> p \<le> \<iota> q"
  by (simp add: test_iso_eq)

lemma test_meet_comm: "\<iota> p \<cdot> \<iota> q = \<iota> q \<cdot> \<iota> p"
  by (metis inf.commute test_inf)

lemma [simp]: "! (\<iota> (p)) + \<iota> p = 1"
  by (metis compl_sup_top test_not test_sup test_top)

lemma [simp]: "\<iota> p + \<iota> (-p) = 1"
  by (metis sup_compl_top test_sup test_top)

lemma [simp]: "\<iota> (-p) \<cdot> \<iota> p = 0"
  by (metis compl_inf_bot test_bot test_inf)

lemma [simp]: "\<iota> p \<cdot> ! (\<iota> p) = 0"
  by (metis inf_compl_bot test_bot test_inf test_not)

end

subsection \<open>Relational and State Transformer Model\<close>

definition rel_atest :: "'a rel \<Rightarrow> 'a rel" ("\<alpha>\<^sub>r") where 
  "\<alpha>\<^sub>r R = Id \<inter> -R"  

interpretation rel_kat: kat "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl "\<alpha>\<^sub>r" 
  by unfold_locales (auto simp: rel_atest_def)

definition sta_atest :: "'a sta \<Rightarrow> 'a sta" ("\<alpha>\<^sub>s") where
  "\<alpha>\<^sub>s f x = \<eta> x - f x"

lemma katest_iff: "y \<in> \<alpha>\<^sub>s f x \<longleftrightarrow> y \<in> \<eta> x \<and> \<not> y \<in> f x"
  unfolding sta_atest_def by simp

declare katest_iff [sta_unfolds]

interpretation sta_kat: kat "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)" kstar "\<alpha>\<^sub>s"
  by unfold_locales (auto simp: sta_unfolds)

lemma r2s_atest: "\<S> (\<alpha>\<^sub>r R) = \<alpha>\<^sub>s (\<S> R)"
  unfolding sta_unfolds s2r_def rel_atest_def 

  by (metis ComplD ComplI IntE IntI r2s_iff  s2r_id) 

lemma s2r_atest: "\<R> (\<alpha>\<^sub>s f) = \<alpha>\<^sub>r (\<R> f)"
  by (metis r2s2r_galois r2s_atest)

lemma p2r_atest [simp]: "\<alpha>\<^sub>r \<lceil>P\<rceil>\<^sub>r = \<lceil>\<lambda>x. \<not> P x\<rceil>\<^sub>r"
  unfolding p2r_def rel_atest_def by force

lemma p2r_test [simp]: "rel_kat.test \<lceil>P\<rceil>\<^sub>r = \<lceil>P\<rceil>\<^sub>r"
  unfolding rel_kat.test_def by force

lemma p2s_atest [simp]: "\<alpha>\<^sub>s \<lceil>P\<rceil>\<^sub>s = \<lceil>\<lambda>x. \<not> P x\<rceil>\<^sub>s"
  unfolding  p2s_def s2p_def sta_atest_def fun_eq_iff by force

lemma p2s_test [simp]: "sta_kat.test \<lceil>P\<rceil>\<^sub>s = \<lceil>P\<rceil>\<^sub>s"
  unfolding sta_kat.test_def by force

end





