(* Title: Propositional Hoare Logic
   Author: Georg Struth
*)

section \<open>Propositional Hoare Logic\<close>

theory PHL
  imports KAT

begin

subsection \<open>Deriving the rules of PHL in KAT\<close>

context kat
begin

definition Ho :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "Ho p x q = (\<tau> p \<cdot> x \<le> x \<cdot> \<tau> q)"

definition while_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while p inv i do x od = while p do x od"

lemma H_def_var: "Ho p x q = (\<tau> p \<cdot> x \<cdot> \<alpha> q = 0)"
  sorry

lemma H_abort: "Ho p 0 q"
  sorry

lemma H_skip: "Ho p 1 p"
  sorry

lemma H_cons: 
  assumes "\<tau> p \<le> \<tau> p'"
  and "Ho p' x q'"
  and "\<tau> q' \<le> \<tau> q"
shows "Ho p x q"
  sorry

lemma H_seq: 
  assumes "Ho r y q"
  and "Ho p x r"
  shows "Ho p (x \<cdot> y) q" 
  sorry

lemma H_cond: 
  assumes "Ho (\<tau> p \<cdot> \<tau> r) x q"
  and "Ho (\<tau> p \<cdot> \<alpha> r) y q"
  shows "Ho p (if r then x else y fi) q"
  sorry

lemma H_cond_iff: "Ho p (if r then x else y fi) q = (Ho (\<tau> p \<cdot> \<tau> r) x q \<and> Ho (\<tau> p \<cdot> \<alpha> r) y q)"
  sorry

lemma H_while: 
  assumes "Ho (\<tau> p \<cdot> \<tau> r) x p"
  shows "Ho p (while r do x od) (\<tau> p \<cdot> \<alpha> r)" 
  sorry

lemma H_inv: 
  assumes "\<tau> p \<le> \<tau> i"
  and "Ho i x i" 
  and "\<tau> i \<le> \<tau> q" 
  shows "Ho p x q"
  sorry

lemma H_inv_seq:
  assumes "Ho i x i"
  and "Ho j x j"
  shows "Ho (\<tau> i \<cdot> \<tau> j) x (\<tau> i \<cdot> \<tau> j)"
  sorry

lemma H_inv_add:
  assumes "Ho i x i"
  and "Ho j x j"
shows "Ho (\<tau> i + \<tau> j) x (\<tau> i + \<tau> j)"
  sorry

lemma H_while_inv: 
  assumes "\<tau> p \<le> \<tau> i"
  and "\<tau> i \<cdot> \<alpha> r \<le> \<tau> q"
  and "Ho (\<tau> i \<cdot> \<tau> r) x i"
shows "Ho p (while r inv i do x od) q" 
  sorry

end


subsection \<open>Hoare Triples in the Relational and State Transformer Model\<close>

text \<open>First we consider relations.\<close>

abbreviation rH :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a pred \<Rightarrow> bool" ("H\<^sub>r") where
  "H\<^sub>r P R Q \<equiv> rel_kat.Ho \<lceil>P\<rceil>\<^sub>r R \<lceil>Q\<rceil>\<^sub>r"

abbreviation rcond :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("rif _ then _ else _ fi" [64,64,64] 63) where
  "rif P then R else S fi \<equiv> rel_kat.cond \<lceil>P\<rceil>\<^sub>r R S"

abbreviation rwhile :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("rwhile _ do _ od" [64,64] 63) where
  "rwhile P do R od \<equiv> rel_kat.while \<lceil>P\<rceil>\<^sub>r R"

abbreviation rwhile_inv :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("rwhile _ inv _ do _ od" [64,64,64] 63) where
  "rwhile P inv I do R od \<equiv> rel_kat.while_inv \<lceil>P\<rceil>\<^sub>r \<lceil>I\<rceil>\<^sub>r R"

lemma rH_unfold: "H\<^sub>r P R Q = (\<forall>x y. P x \<longrightarrow> (x,y) \<in> R \<longrightarrow> Q y)"
  unfolding p2r_def rel_kat.Ho_def rel_kat.test_def rel_atest_def by force
 
lemma rH_skip: "H\<^sub>r P Id Q = (\<forall>x. P x \<longrightarrow> Q x)"
  by (simp add: rH_unfold)

lemma rH_cons1: 
  assumes  "H\<^sub>r P' R Q"
  and "\<forall>x. P x \<longrightarrow> P' x"
  shows "H\<^sub>r P R Q"
  sorry

lemma rH_cons2: 
  assumes "H\<^sub>r P R Q'"
  and "\<forall>x. Q' x \<longrightarrow> Q x"
  shows "H\<^sub>r P R Q"
  sorry

lemma rH_cons: 
  assumes "H\<^sub>r P' R Q'"
  and "\<forall>x. P x \<longrightarrow> P' x"
  and "\<forall>x. Q' x \<longrightarrow> Q x"
 shows "H\<^sub>r P R Q"
  sorry

lemma rH_cond [simp]: "(H\<^sub>r P (rif T then R else S fi) Q) = (H\<^sub>r (\<lambda>s. P s \<and> T s) R Q \<and> H\<^sub>r (\<lambda> s. P s \<and> \<not> T s) S Q)"
  sorry

lemma rH_while_inv: 
  assumes "H\<^sub>r (\<lambda>s. I s \<and> T s) R I"
  and "\<forall>x. P x \<longrightarrow> I x"
  and "\<forall>x. I x \<and> \<not> T x \<longrightarrow> Q x"
  shows "H\<^sub>r P (rwhile T inv I do R od) Q"
  sorry

lemma rH_while: 
  assumes "H\<^sub>r (\<lambda>s. P s \<and> T s) R P"
  shows "H\<^sub>r P (rwhile T do R od) (\<lambda>s. P s \<and> \<not> T s)"
  sorry


text \<open>Next we repeat the development with state transformers.\<close>

abbreviation Hs :: "'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a pred \<Rightarrow> bool" ("H\<^sub>s") where
  "H\<^sub>s P f Q \<equiv> sta_kat.Ho \<lceil>P\<rceil>\<^sub>s f \<lceil>Q\<rceil>\<^sub>s"

abbreviation scond :: "'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" ("sif _ then _ else _ fi" [64,64,64] 63) where
  "sif P then f else g fi \<equiv> sta_kat.cond \<lceil>P\<rceil>\<^sub>s f g"

abbreviation swhile :: "'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a sta" ("swhile _ do _ od" [64,64] 63) where
  "swhile P do f od \<equiv> sta_kat.while \<lceil>P\<rceil>\<^sub>s f"

abbreviation swhile_inv :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a sta \<Rightarrow> 'a sta" ("swhile _ inv _ do _ od" [64,64,64] 63) where
  "swhile P inv I do f od \<equiv> sta_kat.while_inv \<lceil>P\<rceil>\<^sub>s \<lceil>I\<rceil>\<^sub>s f"

lemma sH_unfold: "H\<^sub>s P f Q = (\<forall>x y. P x \<longrightarrow> y \<in> f x \<longrightarrow> Q y)"
  sorry

lemma sH_skip: "H\<^sub>s P \<eta> Q = (\<forall>x. P x \<longrightarrow> Q x)"
  sorry

lemma sH_cons1: 
  assumes "H\<^sub>s P' f Q"
  and "\<forall>x. P x \<longrightarrow> P' x"
  shows "H\<^sub>s P f Q"
  sorry

lemma sH_cons2: 
  assumes "H\<^sub>s P f Q'"
  and "\<forall>x. Q' x \<longrightarrow> Q x" 
  shows "H\<^sub>s P f Q"
  sorry

lemma sH_cons: 
  assumes "H\<^sub>s P' f Q'"
  and "\<forall>x. P x \<longrightarrow> P' x"
  and "\<forall>x. Q' x \<longrightarrow> Q x"
  shows "H\<^sub>s P f Q"
  sorry

lemma sH_cond [simp]: "(H\<^sub>s P (sif T then f else g fi) Q) = (H\<^sub>s (\<lambda>s. P s \<and> T s) f Q \<and> H\<^sub>s (\<lambda> s. P s \<and> \<not>T s) g Q)"
  sorry

lemma sH_while_inv: 
  assumes "H\<^sub>s (\<lambda>s. I s \<and> T s) f I"
  and "\<forall>s. P s \<longrightarrow> I s"
  and "\<forall>s. I s \<and> \<not> T s \<longrightarrow> Q s"
  shows "H\<^sub>s P (swhile T inv I do f od) Q"
  sorry

lemma sH_while: 
  assumes "H\<^sub>s (\<lambda>s. P s \<and> T s) f P"
  shows "H\<^sub>s P (swhile T do f od) (\<lambda>s. P s \<and> \<not> T s)"
  sorry


text \<open>We have taken care that the verification condition generation for relations and state transformers is the same.\<close>

end







