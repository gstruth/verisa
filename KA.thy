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
  assumes mult_comm: "x + y = y + x"


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
  sorry

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

class kleene_algebra = dioid + 
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)
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
  sorry

lemma star_power: "x ^ i \<le> x\<^sup>\<star>"
  sorry

lemma star_trans [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>" 
proof (rule antisym)
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
proof (rule antisym)
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

end

subsection \<open>Linking Algebras with Models by Instantiation\<close>

typedef 'a endo = "{f::'a \<Rightarrow> 'a . True}"
  sorry

setup_lifting type_definition_endo

instantiation endo :: (type) mult_monoid
begin

lift_definition one_endo :: "'a endo" is
  "Abs_endo id".

lift_definition times_endo :: "'a endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo" is
  "\<lambda>x y. Abs_endo (Rep_endo x \<circ> Rep_endo y)".

instance
  by (intro_classes; transfer, simp_all add: Abs_endo_inverse Rep_endo_inverse comp_assoc)

end 

instantiation set :: (type) sup_semilattice
begin

definition plus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "plus_set = (\<lambda>x y. x \<union> y)"

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

text \<open>rel is not a type in Isabelle, so we need to do an interpretation statement instead of an 
instantiation. That for dioids (Proposition 4.5) is trivial because relations are well supported
in Isabelle.\<close>

interpretation rel_d: dioid "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)" 
  by unfold_locales auto 

lemma power_is_relpow: "rel_d.power R i = R ^^ i"
proof (induct i)
  case 0 show ?case
    by simp 
next
  case (Suc i) thus ?case
    by (simp add: relpow_commute) 
qed 

lemma rel_star_def: "R\<^sup>* = (\<Union>i. rel_d.power R i)"
  sorry

lemma rel_star_contl: "R ; S\<^sup>* = (\<Union>i. R ; rel_d.power S i)"
  sorry

lemma rel_star_contr: "R\<^sup>* ; S = (\<Union>i. (rel_d.power R i) ; S)"
  sorry

interpretation rel_ka: kleene_algebra "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl
  sorry

subsection \<open>State Transformer Model of Kleene Algebra\<close>

type_synonym 'a sta = "'a \<Rightarrow> 'a set"

abbreviation eta :: "'a sta" ("\<eta>") where
  "\<eta> x \<equiv> {x}"

abbreviation nsta :: "'a sta" ("\<nu>") where 
  "\<nu> x \<equiv> {}" 

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

lemma kcomp_iff: "y \<in> (f \<circ>\<^sub>K g) x = (\<exists>z. y \<in> g z \<and> z \<in> f x)"
  sorry

lemma kadd_iff: "y \<in> (f +\<^sub>K g) x = (y \<in> f x \<or> y \<in> g x)"
  sorry

lemma kleq_iff: "f \<sqsubseteq> g = (\<forall>x y. y \<in> f x \<longrightarrow> y \<in> g x)"
  sorry

named_theorems sta_unfolds

declare
sta_iff [sta_unfolds]
kcomp_iff [sta_unfolds]
kadd_iff [sta_unfolds]
kleq_iff [sta_unfolds]

lemma kcomp_assoc: "(f \<circ>\<^sub>K g) \<circ>\<^sub>K h = f \<circ>\<^sub>K (g \<circ>\<^sub>K h)"
proof-
  {fix x y
  have "y \<in> ((f \<circ>\<^sub>K g) \<circ>\<^sub>K h) x = (\<exists>v. y \<in> h v \<and>  (\<exists>w. v \<in> g w \<and> w \<in> f x))"
    unfolding sta_unfolds by simp
  also have "\<dots> = (\<exists>v w. y \<in> h v \<and> v \<in> g w \<and> w \<in> f x)"
    by blast
  also have "\<dots> = (\<exists>w. (\<exists>v. y \<in> h v \<and> v \<in> g w) \<and> w \<in> f x)"
    by blast
  also have "\<dots> = (y \<in> (f \<circ>\<^sub>K (g \<circ>\<^sub>K h)) x)"
    unfolding sta_unfolds by simp
  finally have "y \<in> ((f \<circ>\<^sub>K g) \<circ>\<^sub>K h) x = (y \<in> (f \<circ>\<^sub>K (g \<circ>\<^sub>K h)) x)".}
  thus ?thesis
    unfolding sta_unfolds by simp
qed

interpretation sta_monm: monoid_mult "\<eta>" "(\<circ>\<^sub>K)"
  sorry

interpretation sta_di: dioid "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)"
  sorry

abbreviation "kpow \<equiv> sta_monm.power"

definition kstar :: "'a sta \<Rightarrow> 'a sta" where
  "kstar f x = (\<Union>i. kpow f i x)"

lemma kstar_iff: "y \<in> kstar f x = (\<exists>i. y \<in> kpow f i x)"
  unfolding kstar_def by blast

declare kstar_iff [sta_unfolds]

lemma kstar_unfoldl: "\<eta> +\<^sub>K f \<circ>\<^sub>K kstar f \<sqsubseteq> kstar f"
  sorry 

lemma kstar_unfoldr: "\<eta> +\<^sub>K kstar f \<circ>\<^sub>K f \<sqsubseteq> kstar f"
  sorry

lemma kstar_contl: "(f \<circ>\<^sub>K kstar g) x = (\<Union>i. (f \<circ>\<^sub>K kpow g i) x)"
  sorry

lemma kstar_contr: "(kstar f \<circ>\<^sub>K g) x = (\<Union>i. (kpow f i \<circ>\<^sub>K g) x)"
  sorry

lemma kstar_inductl: "h +\<^sub>K f \<circ>\<^sub>K g \<sqsubseteq> g \<Longrightarrow> kstar f \<circ>\<^sub>K h \<sqsubseteq> g"
  sorry

lemma kstar_inductr: "h +\<^sub>K g \<circ>\<^sub>K f \<sqsubseteq> g \<Longrightarrow> h \<circ>\<^sub>K kstar f \<sqsubseteq> g"
  sorry

interpretation sta_ka: kleene_algebra "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)" kstar
  sorry

subsection \<open>Isomorphism between the models\<close>

definition r2s :: "'a rel \<Rightarrow> 'a sta" ("\<S>") where
  "\<S> R = Image R \<circ> \<eta>" 

definition s2r :: "'a sta \<Rightarrow> 'a rel" ("\<R>") where
  "\<R> f = {(x,y). y \<in> f x}"

lemma r2s_iff: "y \<in> \<S> R x \<longleftrightarrow> (x,y) \<in> R"
  by (simp add: r2s_def)

lemma s2r_iff: "(x,y) \<in> \<R> f \<longleftrightarrow> y \<in> f x"
  sorry

text \<open>The functors form a bijective pair.\<close>

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

lemma s2r_comp: "\<S> (R ; S) = \<S> R \<circ>\<^sub>K \<S> S"
  sorry

lemma r2s_comp: "\<R> (f \<circ>\<^sub>K g) = \<R> f ; \<R> g"
  sorry

lemma s2r_id: "\<S> Id = \<eta>"
  sorry

lemma r2s_id: "\<R> \<eta> = Id"
  sorry

lemma s2r_zero: "\<S> {} = \<nu>"
  sorry

lemma r2s_zero: "\<R> \<nu> = {}"
  sorry

lemma r2s_add: "\<S> (R \<union> S) = \<S> R +\<^sub>K \<S> S"
  sorry

lemma s2r_add: "\<R> (f +\<^sub>K g) = \<R> f \<union> \<R> g"
  sorry

lemma s2r_pow: "\<S> (rel_d.power R i) = kpow (\<S> R) i"
  sorry

lemma s2r_star: "\<S> (R\<^sup>*) = kstar (\<S> R)"
  sorry

lemma r2s_pow: "rel_d.power (\<R> f) i = \<R> (kpow f i)"
  sorry

lemma r2s_star: "\<R> (kstar f) = (\<R> f)\<^sup>*"
  sorry

lemma kcomp_assoc2: "(f \<circ>\<^sub>K g) \<circ>\<^sub>K h = f \<circ>\<^sub>K (g \<circ>\<^sub>K h)"
  sorry


subsection \<open>Embedding Predicates into State Transformers and Relations\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

notation inf (infixl "\<sqinter>" 70) 
notation sup (infixl "\<squnion>" 65)

text \<open>First we consider relations.\<close>

definition p2r :: "'a pred \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>\<^sub>r") where
  "\<lceil>P\<rceil>\<^sub>r = {(s,s) |s. P s}"

definition r2p :: "'a rel \<Rightarrow> 'a pred" ("\<lfloor>_\<rfloor>\<^sub>r")where
  "\<lfloor>R\<rfloor>\<^sub>r \<equiv> (\<lambda>s. s \<in> Domain R)"

lemma r2p2r [simp]: "\<lfloor>\<lceil>P\<rceil>\<^sub>r\<rfloor>\<^sub>r = P"
  unfolding p2r_def r2p_def by force

lemma p2r2p: "R \<subseteq> Id \<Longrightarrow> \<lceil>\<lfloor>R\<rfloor>\<^sub>r\<rceil>\<^sub>r = R"
  unfolding p2r_def r2p_def by force

lemma p2r_r2p_galois: "R \<subseteq> Id \<Longrightarrow> (\<lfloor>R\<rfloor>\<^sub>r = P) = (R = \<lceil>P\<rceil>\<^sub>r)"
  using p2r2p by auto

lemma p2r_comp [simp]: "\<lceil>P\<rceil>\<^sub>r ; \<lceil>Q\<rceil>\<^sub>r = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>\<^sub>r" 
  unfolding p2r_def by auto

lemma r2p_comp: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> \<lfloor>R ; S\<rfloor>\<^sub>r = (\<lambda>s. \<lfloor>R\<rfloor>\<^sub>r s \<and> \<lfloor>S\<rfloor>\<^sub>r s)" 
  unfolding r2p_def by force

lemma p2r_imp [simp]: "\<lceil>P\<rceil>\<^sub>r \<subseteq> \<lceil>Q\<rceil>\<^sub>r = (\<forall>s. P s \<longrightarrow> Q s)"
  unfolding p2r_def by force

text \<open>Next we repeat the development with state transformers.\<close>

definition p2s :: "'a pred \<Rightarrow> 'a sta" ("\<lceil>_\<rceil>\<^sub>s") where
  "\<lceil>P\<rceil>\<^sub>s x \<equiv> if P x then {x} else {}"

definition s2p :: "'a sta \<Rightarrow> 'a pred" ("\<lfloor>_\<rfloor>\<^sub>s")where
  "\<lfloor>f\<rfloor>\<^sub>s s \<equiv> (f s \<noteq> {})"

lemma s2p2s [simp]: "\<lfloor>\<lceil>P\<rceil>\<^sub>s\<rfloor>\<^sub>s = P"
  unfolding p2s_def s2p_def by force

lemma p2s2p: "f \<sqsubseteq> \<eta> \<Longrightarrow> \<lceil>\<lfloor>f\<rfloor>\<^sub>s\<rceil>\<^sub>s = f"
  unfolding p2s_def s2p_def sta_iff kleq_iff by force 

lemma p2s_s2p_galois: "f \<sqsubseteq> \<eta> \<Longrightarrow> (\<lfloor>f\<rfloor>\<^sub>s = P) = (f = \<lceil>P\<rceil>\<^sub>s)"
  unfolding p2s_def s2p_def sta_iff kleq_iff by force

lemma p2s_comp [simp]: "\<lceil>P\<rceil>\<^sub>s \<circ>\<^sub>K \<lceil>Q\<rceil>\<^sub>s = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>\<^sub>s" 
  unfolding  p2s_def s2p_def sta_iff kcomp_iff by force

lemma s2p_comp: "f \<sqsubseteq> \<eta> \<Longrightarrow> g \<sqsubseteq> \<eta> \<Longrightarrow> \<lfloor>f \<circ>\<^sub>K g\<rfloor>\<^sub>s = (\<lambda>s. \<lfloor>f\<rfloor>\<^sub>s s \<and> \<lfloor>g\<rfloor>\<^sub>s s)" 
  unfolding s2p_def kleq_iff kcomp_iff kcomp_def by blast

lemma p2s_imp [simp]: "\<lceil>P\<rceil>\<^sub>s \<sqsubseteq> \<lceil>Q\<rceil>\<^sub>s = (\<forall>s. P s \<longrightarrow> Q s)"
  unfolding  p2s_def s2p_def kleq_iff by simp

lemma p2r2s: "\<lceil>P\<rceil>\<^sub>s = \<S> \<lceil>P\<rceil>\<^sub>r"
  unfolding p2r_def p2s_def sta_iff r2s_iff by simp

lemma p2s2r: "\<lceil>P\<rceil>\<^sub>r = \<R> \<lceil>P\<rceil>\<^sub>s"
  by (metis (no_types) p2r2s r2s2r_galois)

end





