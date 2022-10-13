(* Title: Kleene Algebra
   Author: Georg Struth
*)

section \<open>Kleene Algebra\<close>

theory KA
  imports Main

begin

subsection \<open>Monoids\<close>

notation times (infixl "\<cdot>" 70)

class mult_monoid = times + one +
  assumes mult_assoc: "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
  and mult_unitl: "1 \<cdot> x = x"
  and mult_unitr: "x \<cdot> 1 = x"

class add_monoid = plus + zero +
  assumes add_assoc: "x + (y + z) = (x + y) + z"
  and add_unitl: "0 + x = x"
  and add_unitr: "x + 0 = x"

class abelian_add_monoid = add_monoid +
  assumes add_comm: "x + y = y + x"


subsection \<open>Semilattices\<close>

class sup_semilattice = comm_monoid_add + ord +
  assumes add_idem: "x + x = x"
  and order_def: "x \<le> y \<longleftrightarrow> x + y = y"
  and strict_order_def: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

begin

subclass order 
  sorry

lemma zero_least: "0 \<le> x"
  sorry

lemma add_isor: "x \<le> y \<Longrightarrow> x + z \<le> y + z" 
proof-
  assume "x \<le> y"
  hence a: "x + y = y"
    by (simp add: order_def)
  have "x + z + y + z = x + y + z"
    by (metis add_commute local.add_assoc local.add_idem)
  also have "\<dots> = y + z"
    by (simp add: a)
  finally have "x + z + y + z = y + z".
  thus "x + z \<le> y + z"
    by (simp add: add_assoc order_def)
qed

lemma add_isol: "x \<le> y \<Longrightarrow> z + x \<le> z + y"
  sorry

lemma add_iso: "x \<le> y \<Longrightarrow> x' \<le> y' \<Longrightarrow> x + x' \<le> y + y'"
  sorry

lemma add_ubl: "x \<le> x + y" 
  sorry

lemma add_ubr: "y \<le> x + y"
  sorry

lemma add_least: "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x + y \<le> z"
  sorry

lemma add_lub: "(x + y \<le> z) = (x \<le> z \<and> y \<le> z)"
  using add_least add_ubl add_ubr dual_order.trans by blast

end


subsection \<open>Semirings and Dioids\<close>

class semiring = comm_monoid_add + monoid_mult +
  assumes distl: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
  and distr: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and annil [simp]: "0 \<cdot> x = 0"
  and annir [simp]: "x \<cdot> 0 = 0"

class dioid = semiring + sup_semilattice

begin

lemma mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  sorry

lemma mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  sorry

lemma mult_iso: "x \<le> y \<Longrightarrow> x' \<le> y' \<Longrightarrow> x \<cdot> x' \<le> y \<cdot> y'"
  sorry

end


subsection \<open>Kleene Algebras\<close>

class star = 
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)

class kleene_algebra = dioid + star +
  assumes star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"  
  and star_unfoldr: "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  and star_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and star_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"

begin

lemma one_le_star: "1 \<le> x\<^sup>\<star>"
proof-
  have "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: star_unfoldl) 
  thus "1 \<le> x\<^sup>\<star>"
    by (simp add: add_lub)
qed

lemma star_unfoldlr: "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  sorry

lemma star_unfoldrr: "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  sorry

lemma star_infl: "x \<le> x\<^sup>\<star>" 
proof-
  have "x = x \<cdot> 1"
    by simp
  also have "\<dots> \<le> x \<cdot> x\<^sup>\<star>"
    using mult_isol one_le_star by force
  also have "\<dots> \<le> x\<^sup>\<star>"
    by (simp add: star_unfoldlr)
  finally show "x \<le> x\<^sup>\<star>".
qed

lemma star_power: "x ^ i \<le> x\<^sup>\<star>"
proof (induct i)
case 0
  show "x ^ 0 \<le> x\<^sup>\<star>"
    by (simp add: one_le_star)
next
  case (Suc i)
  assume "x ^ i \<le> x\<^sup>\<star>"
  have "x ^ Suc i = x \<cdot> x ^ i"
    by simp
  also have "\<dots> \<le> x \<cdot> x\<^sup>\<star>"
    by (simp add: Suc.hyps mult_isol)
  also have "\<dots>  \<le> x\<^sup>\<star>"
    by (simp add: star_unfoldlr)
  finally show "x ^ Suc i \<le> x\<^sup>\<star>".
qed

lemma star_trans [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>" 
proof (rule order.antisym)
  have "x\<^sup>\<star> + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: add_least star_unfoldlr)
  thus "x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: star_inductl)
  have "x\<^sup>\<star> = 1 \<cdot> x\<^sup>\<star>"
    by simp
  also have "\<dots> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    using mult_isor one_le_star by force
  finally show "x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star>".
qed

lemma star_idem [simp]: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>" 
  sorry

lemma star_unfoldl_eq [simp]: "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"  
  sorry

lemma star_unfoldr_eq [simp]: "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  sorry

lemma star_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>" 
  sorry

lemma star_slide: "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>" 
  sorry

lemma star_denest: "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>" 
proof (rule order.antisym)
  have a: "1 \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult_1_right mult_isol order_trans one_le_star)
  have b: "x \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: mult_isor star_unfoldlr)
  have "y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: star_unfoldlr)
  also have  "\<dots> = 1 \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by simp
  also have "\<dots> \<le>  x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    using mult_isor one_le_star by blast
  finally have "y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>".
  hence "1 + (x + y) \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: a b add_lub distr)
  thus  "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    using mult_assoc star_inductl by fastforce
  have a: "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (simp add: add_ubl star_iso)
  have "y \<le> (x + y)\<^sup>\<star>"
    using add_lub star_infl by blast
  hence "(y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> ((x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star>)\<^sup>\<star>"
    using a mult_iso star_iso by blast
  also have "\<dots> = (x + y)\<^sup>\<star>"
    by simp
  finally have "(y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>".
  hence "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star>"
    using a mult_iso by blast
  also have "\<dots> \<le> (x + y)\<^sup>\<star>"
    by simp
  finally show "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>".
qed

lemma star_subid: "x \<le> 1 \<Longrightarrow> x\<^sup>\<star> = 1"
  sorry

lemma star_subid_iff: "(x\<^sup>\<star> = 1) = (x \<le> 1)"
  sorry

lemma zero_star [simp]: "0\<^sup>\<star> = 1" 
  sorry

lemma one_star [simp]: "1\<^sup>\<star> = 1" 
  sorry

lemma star_sim1: "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z" 
  sorry

lemma star_sim2: "x \<cdot> z \<le> z \<cdot> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z  \<le> z \<cdot> y\<^sup>\<star>"
  sorry

lemma star_inductl_var: "x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y" 
  sorry

lemma star_inductr_var: "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  sorry

lemma church_rosser: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<Longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>" 
  sorry

lemma power_sup: "((\<Sum>i=0..n. x^i) \<le> y) = (\<forall>i. 0 \<le> i \<and> i \<le> n \<longrightarrow> x^i \<le> y)"
  sorry

lemma power_dist: "(\<Sum>i=0..n. x ^ i) \<cdot> x = (\<Sum>i=0..n. x ^ Suc i)"
  sorry

lemma power_sum: "(\<Sum>i=0..n. x ^ Suc i) = (\<Sum>i=1..n. x ^ i) + x ^ Suc n"
  sorry

lemma sum_star: "x\<^sup>\<star> = (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x ^ i)"
  sorry

lemma idem_prop: "x \<cdot> x = x \<Longrightarrow> (x \<cdot> y)\<^sup>\<star> \<cdot> x = (x \<cdot> y \<cdot> x)\<^sup>\<star> \<cdot> x"
  sorry

end

subsection \<open>Linking Algebras with Models by Instantiation and Interpretation\<close>

instantiation nat :: mult_monoid
begin

instance
proof
  fix x y z :: nat
  show "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
    by simp
  show "1 \<cdot> x = x"
    by simp
  show "x \<cdot> 1 = x "
    by simp
qed

end

instantiation nat :: abelian_add_monoid
begin

instance
proof
  fix x y z :: nat
  show "x + (y + z) = (x + y) + z"
    by simp
  show "0 + x = x"
    by simp
  show "x + 0 = x "
    by simp
  show "x + y = y + x"
    by simp
qed

end

typedef 'a endo = "{f::'a \<Rightarrow> 'a . True}"
  by simp

setup_lifting type_definition_endo

instantiation endo :: (type) mult_monoid
begin

lift_definition one_endo :: "'a endo" is
  "Abs_endo id".

lift_definition times_endo :: "'a endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo" is
  "\<lambda>x y. Abs_endo (Rep_endo x \<circ> Rep_endo y)".

instance
  sorry

end 

instantiation set :: (type) sup_semilattice
begin

definition plus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "plus_set x y = x \<union> y"

definition zero_set :: "'a set" where 
  "zero_set = {}"

instance 
  sorry

end

interpretation inter_sl: sup_semilattice "(\<inter>)" UNIV "(\<supseteq>)" "(\<supset>)"
  sorry

context dioid
begin

lemma power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x ^ i \<cdot> z \<le> y"
  sorry

lemma power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ i \<le> y"
  sorry

end

subsection \<open>Relational Model of Kleene algebra\<close>

notation relcomp (infixl ";" 70)

interpretation rel_d: dioid "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)"
  sorry

lemma power_is_relpow: "rel_d.power R i = R ^^ i"
  by (induct i) (simp_all add: relpow_commute)

lemma rel_star_def: "R\<^sup>* = (\<Union>i. rel_d.power R i)"
  sorry

lemma rel_star_contl: "R ; S\<^sup>* = (\<Union>i. R ; rel_d.power S i)"
  sorry

lemma rel_star_contr: "R\<^sup>* ; S = (\<Union>i. (rel_d.power R i) ; S)"
  sorry

lemma rel_star_unfoldl: "Id \<union> R ; R\<^sup>* = R\<^sup>*"
  sorry

lemma rel_star_unfoldr: "Id \<union> R\<^sup>* ; R = R\<^sup>*"
  sorry

lemma rel_star_inductl: 
  fixes R S T :: "'a rel"
  assumes "T \<union> R ; S \<subseteq> S"
  shows "R\<^sup>* ; T \<subseteq> S"
  sorry

lemma rel_star_inductr: "(T::'a rel) \<union> S ; R \<subseteq> S \<Longrightarrow> T ; R\<^sup>* \<subseteq> S"
  sorry

interpretation rel_ka: kleene_algebra "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl
  sorry


subsection \<open>State Transformer Model of Kleene Algebra\<close>

type_synonym 'a sta = "'a \<Rightarrow> 'a set"

definition eta :: "'a sta" ("\<eta>") where
  "\<eta> x = {x}"

definition nsta :: "'a sta" ("\<nu>") where 
  "\<nu> x = {}" 

definition kcomp :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" (infixl "\<circ>\<^sub>K" 75) where
  "(f \<circ>\<^sub>K g) x = \<Union>{g y |y. y \<in> f x}"

definition kadd :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" (infixl "+\<^sub>K" 65) where
  "(f +\<^sub>K g) x = f x \<union> g x" 

definition kleq :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "f \<sqsubseteq> g = (\<forall>x. f x \<subseteq> g x)"

definition kle :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
  "f \<sqsubset> g = (f \<sqsubseteq> g \<and> f \<noteq> g)"

lemma sta_iff: "((f::'a sta) = g) = (\<forall>x y. y \<in> f x \<longleftrightarrow> y \<in> g x)"
  sorry

lemma eta_iff: "y \<in> \<eta> x = (y = x)"
  sorry

lemma nsta_iff: "y \<notin> \<nu> x"
  sorry

lemma kcomp_iff: "y \<in> (f \<circ>\<^sub>K g) x = (\<exists>z. y \<in> g z \<and> z \<in> f x)"
  sorry

lemma kadd_iff: "y \<in> (f +\<^sub>K g) x = (y \<in> f x \<or> y \<in> g x)"
  sorry

lemma kleq_iff: "f \<sqsubseteq> g = (\<forall>x y. y \<in> f x \<longrightarrow> y \<in> g x)"
  sorry

lemma kcomp_assoc: "(f \<circ>\<^sub>K g) \<circ>\<^sub>K h = f \<circ>\<^sub>K (g \<circ>\<^sub>K h)"
proof-
  {fix x y
  have "y \<in> ((f \<circ>\<^sub>K g) \<circ>\<^sub>K h) x = (\<exists>v. y \<in> h v \<and> (\<exists>w. v \<in> g w \<and> w \<in> f x))"
    unfolding kcomp_iff by simp
  also have "\<dots> = (\<exists>w. (\<exists>v. y \<in> h v \<and> v \<in> g w) \<and> w \<in> f x)"
    by force
  also have "\<dots> = (y \<in> (f \<circ>\<^sub>K (g \<circ>\<^sub>K h)) x)"
    unfolding kcomp_iff by simp
  finally have "y \<in> ((f \<circ>\<^sub>K g) \<circ>\<^sub>K h) x = (y \<in> (f \<circ>\<^sub>K (g \<circ>\<^sub>K h)) x)".}
  thus ?thesis
    by force
qed


text \<open>The following two functors yield isomorphism between the relational and state transformer model\<close>

definition r2s :: "'a rel \<Rightarrow> 'a sta" ("\<S>") where
  "\<S> R = Image R \<circ> \<eta>" 

definition s2r :: "'a sta \<Rightarrow> 'a rel" ("\<R>") where
  "\<R> f = {(x,y). y \<in> f x}"

lemma r2s_iff: "y \<in> \<S> R x \<longleftrightarrow> (x,y) \<in> R"
  by (simp add: r2s_def eta_def)

lemma s2r_iff: "(x,y) \<in> \<R> f \<longleftrightarrow> y \<in> f x"
  by (simp add: s2r_def)

lemma r2s2r_inv1 [simp]: "\<R> \<circ> \<S> = id"
  sorry

lemma s2r2s_inv2 [simp]: "\<S> \<circ> \<R> = id"
  sorry

lemma r2s2r_galois: "(\<R> f = R) = (\<S> R = f)"
  sorry

lemma r2s_inj: "inj \<S>"
  sorry

lemma s2r_inj: "inj \<R>"
  sorry

lemma r2s_surj: "surj \<S>"
  sorry

lemma s2r_surj: "surj \<R>"
  sorry

lemma r2s_bij: "bij \<S>"
  sorry

lemma s2r_bij: "bij \<R>"
  sorry

lemma r2s_comp: "\<R> (f \<circ>\<^sub>K g) = \<R> f ; \<R> g"
  sorry

lemma s2r_comp: "\<S> (R ; S) = \<S> R \<circ>\<^sub>K \<S> S"
  sorry

lemma r2s_id: "\<R> \<eta> = Id"
  sorry

lemma s2r_id: "\<S> Id = \<eta>"
  sorry

lemma r2s_zero: "\<R> \<nu> = {}"
  sorry

lemma s2r_zero: "\<S> {} = \<nu>"
  sorry

lemma s2r_add: "\<R> (f +\<^sub>K g) = \<R> f \<union> \<R> g"
  sorry

lemma r2s_add: "\<S> (R \<union> S) = \<S> R +\<^sub>K \<S> S"
  sorry

lemma type_definition_s2r_r2s: "type_definition \<R> \<S> UNIV"
  unfolding type_definition_def by (meson iso_tuple_UNIV_I r2s2r_galois)

definition "rel_s2r R f = (R = \<R> f)"

lemma bi_unique_rel_s2r [transfer_rule]: "bi_unique rel_s2r"
  sorry

lemma bi_total_rel_s2r [transfer_rule]: "bi_total rel_s2r"
  sorry

lemma Id_eta_transfer [transfer_rule]: "rel_s2r Id \<eta>"
  sorry

lemma emp_nsta_transfer [transfer_rule]: "rel_s2r {} \<nu>"
  sorry

lemma relcomp_kcomp_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r rel_s2r) (;) (\<circ>\<^sub>K)"
  sorry

lemma un_kadd_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r rel_s2r) (\<union>) (+\<^sub>K)"
  sorry

lemma leq_kleq_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r (=)) (\<subseteq>) (\<sqsubseteq>)"
  sorry

lemma le_kle_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r (=)) (\<subset>) (\<sqsubset>)"
  sorry

text \<open>Next we show that state transformers form dioids using this translation.\<close>

interpretation sta_monm: monoid_mult "\<eta>" "(\<circ>\<^sub>K)"
  sorry

interpretation sta_di: dioid "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)"
  sorry

text \<open>The monoid interpretation is helpful for defining the Kleene star.\<close>

abbreviation "kpow \<equiv> sta_monm.power"

definition kstar :: "'a sta \<Rightarrow> 'a sta" where
  "kstar f x = (\<Union>i. kpow f i x)"

text \<open>We can now extend the isomorphism from dioids to Kleene algebras.\<close>

lemma r2s_pow: "rel_d.power (\<R> f) i = \<R> (kpow f i)"
  sorry

lemma r2s_star: "\<R> (kstar f) = (\<R> f)\<^sup>*"
proof-
  {fix x y
    have "(x,y) \<in> \<R> (kstar f) = (\<exists>i. y \<in> kpow f i x)"
      by (simp add: kstar_def s2r_def)
    also have "\<dots> = ((x,y) \<in> (\<Union>i. \<R> (kpow f i)))"
      unfolding s2r_def by simp
    also have "\<dots> = ((x,y) \<in> (\<Union>i. rel_d.power (\<R> f) i))"
      using r2s_pow by fastforce
    finally have "(x,y) \<in> \<R> (kstar f) = ((x,y) \<in> (\<R> f)\<^sup>*)"
      using rel_star_def by blast}
  thus ?thesis
    by auto
qed

lemma s2r_pow: "\<S> (rel_d.power R i) = kpow (\<S> R) i"
  sorry

lemma s2r_star: "\<S> (R\<^sup>*) = kstar (\<S> R)"
  sorry

text \<open>Finally we prove that state transformers form Kleene algebras.\<close>

lemma rtrancl_kstar_transfer [transfer_rule]: "rel_fun rel_s2r rel_s2r rtrancl kstar"
  sorry

interpretation sta_ka: kleene_algebra "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)" kstar
  sorry

subsection \<open>Embedding Predicates into State Transformers and Relations\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

text \<open>First we consider relations.\<close>

definition p2r :: "'a pred \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>\<^sub>r") where
  "\<lceil>P\<rceil>\<^sub>r = {(s,s) |s. P s}"

definition r2p :: "'a rel \<Rightarrow> 'a pred" ("\<lfloor>_\<rfloor>\<^sub>r")where
  "\<lfloor>R\<rfloor>\<^sub>r \<equiv> (\<lambda>s. s \<in> Domain R)"

lemma r2p2r [simp]: "\<lfloor>\<lceil>P\<rceil>\<^sub>r\<rfloor>\<^sub>r = P"
  sorry

lemma p2r2p: "R \<subseteq> Id \<Longrightarrow> \<lceil>\<lfloor>R\<rfloor>\<^sub>r\<rceil>\<^sub>r = R"
  sorry

lemma p2r_r2p_galois: "R \<subseteq> Id \<Longrightarrow> (\<lfloor>R\<rfloor>\<^sub>r = P) = (R = \<lceil>P\<rceil>\<^sub>r)"
  sorry

lemma p2r_comp [simp]: "\<lceil>P\<rceil>\<^sub>r ; \<lceil>Q\<rceil>\<^sub>r = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>\<^sub>r" 
  sorry

lemma r2p_comp: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> \<lfloor>R ; S\<rfloor>\<^sub>r = (\<lambda>s. \<lfloor>R\<rfloor>\<^sub>r s \<and> \<lfloor>S\<rfloor>\<^sub>r s)" 
  sorry

lemma p2r_imp [simp]: "\<lceil>P\<rceil>\<^sub>r \<subseteq> \<lceil>Q\<rceil>\<^sub>r = (\<forall>s. P s \<longrightarrow> Q s)"
  sorry

text \<open>Next we repeat the development with state transformers.\<close>

definition p2s :: "'a pred \<Rightarrow> 'a sta" ("\<lceil>_\<rceil>\<^sub>s") where
  "\<lceil>P\<rceil>\<^sub>s x \<equiv> if P x then {x} else {}"

definition s2p :: "'a sta \<Rightarrow> 'a pred" ("\<lfloor>_\<rfloor>\<^sub>s")where
  "\<lfloor>f\<rfloor>\<^sub>s s \<equiv> (f s \<noteq> {})"

lemma s2p2s [simp]: "\<lfloor>\<lceil>P\<rceil>\<^sub>s\<rfloor>\<^sub>s = P"
  sorry

lemma p2s2p: "f \<sqsubseteq> \<eta> \<Longrightarrow> \<lceil>\<lfloor>f\<rfloor>\<^sub>s\<rceil>\<^sub>s = f"
  sorry

lemma p2s_s2p_galois: "f \<sqsubseteq> \<eta> \<Longrightarrow> (\<lfloor>f\<rfloor>\<^sub>s = P) = (f = \<lceil>P\<rceil>\<^sub>s)"
  sorry

lemma p2s_comp [simp]: "\<lceil>P\<rceil>\<^sub>s \<circ>\<^sub>K \<lceil>Q\<rceil>\<^sub>s = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>\<^sub>s" 
  sorry

lemma s2p_comp: "f \<sqsubseteq> \<eta> \<Longrightarrow> g \<sqsubseteq> \<eta> \<Longrightarrow> \<lfloor>f \<circ>\<^sub>K g\<rfloor>\<^sub>s = (\<lambda>s. \<lfloor>f\<rfloor>\<^sub>s s \<and> \<lfloor>g\<rfloor>\<^sub>s s)" 
  sorry

lemma p2s_imp [simp]: "\<lceil>P\<rceil>\<^sub>s \<sqsubseteq> \<lceil>Q\<rceil>\<^sub>s = (\<forall>s. P s \<longrightarrow> Q s)"
  sorry

lemma p2r2s: "\<lceil>P\<rceil>\<^sub>s = \<S> \<lceil>P\<rceil>\<^sub>r"
  sorry

lemma p2s2r: "\<lceil>P\<rceil>\<^sub>r = \<R> \<lceil>P\<rceil>\<^sub>s"
  sorry

end





