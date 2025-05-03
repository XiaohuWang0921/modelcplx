theory Cplx
  imports Main
begin

section \<open>Theory of model complexes\<close>

subsection \<open>Stuff missing from the standard library\<close>

definition flip :: "[['a, 'b] \<Rightarrow> 'c, 'b, 'a] \<Rightarrow> 'c"
  where "flip = (\<lambda>f x y. f y x)"

definition uncurry :: "[['a, 'b] \<Rightarrow> 'c, 'a \<times> 'b] \<Rightarrow> 'c"
  where "uncurry = (\<lambda>f (x, y). f x y)"

definition join :: "[['a, 'a] \<Rightarrow> 'b, 'a] \<Rightarrow> 'b"
  where "join = (\<lambda>f x. f x x)"

definition const :: "['a, 'b] \<Rightarrow> 'a"
  where "const = (\<lambda>x _. x)"

definition dup :: "'a \<Rightarrow> 'a \<times> 'a"
  where "dup = (\<lambda>x. (x, x))"

lemma flip_conv [simp]: "flip f x y = f y x"
  unfolding flip_def by rule

lemma uncurry_conv: "uncurry f (x, y) = f x y"
  unfolding uncurry_def by simp

lemma uncurry_apply [simp]: "uncurry f p = f (fst p) (snd p)"
  using split_pairs uncurry_conv by metis

lemma flip_flip [simp]: "flip (flip f) = f"
  unfolding flip_def by rule

lemma curry_uncurry [simp]: "curry (uncurry f) = f"
  unfolding uncurry_def by simp

lemma uncurry_curry [simp]: "uncurry (curry f) = f"
  unfolding curry_def by rule simp 

lemma const_apply [simp]: "const x y = x"
  unfolding const_def by rule

lemma join_apply [simp]: "join f x = f x x"
  unfolding join_def by rule

lemma flip_const [simp]: "flip const = const id"
  unfolding flip_def const_def id_def by rule

lemma join_flip [simp]: "join (flip f) = join f"
  unfolding join_def by simp

lemma swap_dup [simp]: "prod.swap (dup x) = dup x"
  unfolding dup_def by simp

lemma dup_apply [simp]: "dup x = (x, x)"
  unfolding dup_def by rule

lemma uncurry_dup [simp]: "uncurry f (dup x) = join f x"
  unfolding dup_def by simp

subsection \<open>Definition\<close>

typedecl \<Delta>
typedecl \<Lambda>

axiomatization emb :: "\<Lambda> \<Rightarrow> \<Delta>"

class cplx =
  fixes fill :: "[\<Lambda> \<Rightarrow> 'a, \<Delta>] \<Rightarrow> 'a"
  assumes sec [simp]: "fill h (emb l) = h l"
  assumes proj [simp]: "fill (\<lambda>_. x) d = x" (* Weakening *)
  assumes diag [simp]: "fill (\<lambda>l. fill (hh l) d) d = fill (\<lambda>l. hh l l) d" (* Contraction *)
  assumes braid: "fill (\<lambda>l. fill (hh l) d') d = fill (\<lambda>l. fill (\<lambda>l'. hh l' l) d) d'" (* Permutation *)
        (* Can't make braid a [simp] because it causes cycle *)

subsection \<open>Obvious constructions\<close>

instantiation "fun" :: (type, cplx) cplx
begin

definition fill_fun: "fill h d x = fill (flip h x) d"

instance proof
  fix h :: "[\<Lambda>, 'a] \<Rightarrow> 'b"
  fix l :: \<Lambda>
  show "fill h (emb l) = h l" unfolding fill_fun by simp
next
  fix f :: "'a \<Rightarrow> 'b"
  fix d :: \<Delta>
  show "fill (\<lambda>_. f) d = f" unfolding fill_fun flip_def by simp
next
  fix hh :: "[\<Lambda>, \<Lambda>, 'a] \<Rightarrow> 'b"
  fix d :: \<Delta>
  show "fill (\<lambda>l. fill (hh l) d) d = fill (\<lambda>l. hh l l) d"
    unfolding fill_fun flip_def by simp
next
  fix hh :: "[\<Lambda>, \<Lambda>, 'a] \<Rightarrow> 'b"
  fix d d' :: \<Delta>
  show "fill (\<lambda>l. fill (hh l) d') d = fill (\<lambda>l. fill (\<lambda>l'. hh l' l) d) d'"
    unfolding fill_fun flip_def by rule (rule braid)
qed

end

instantiation prod :: (cplx, cplx) cplx
begin

definition fill_prod: "fill h d = (fill (fst \<circ> h) d, fill (snd \<circ> h) d)"

instance proof
  fix h :: "\<Lambda> \<Rightarrow> 'a \<times> 'b"
  fix l :: \<Lambda>
  show "fill h (emb l) = h l"
    unfolding fill_prod by simp
next
  fix x :: "'a \<times> 'b"
  fix d :: \<Delta>
  show "fill (\<lambda>_. x) d = x"
    unfolding fill_prod comp_def by simp
next
  fix hh :: "[\<Lambda>, \<Lambda>] \<Rightarrow> 'a \<times> 'b"
  fix d :: \<Delta>
  show "fill (\<lambda>l. fill (hh l) d) d = fill (\<lambda>l. hh l l) d"
    unfolding fill_prod comp_def by (simp add: prod_eq_iff)
next
  fix hh :: "[\<Lambda>, \<Lambda>] \<Rightarrow> 'a \<times> 'b"
  fix d d' :: \<Delta>
  show "fill (\<lambda>l. fill (\<lambda>l'. hh l' l) d) d' = fill (\<lambda>l. fill (hh l) d') d"
    unfolding fill_prod comp_def by (simp add: prod_eq_iff, rule) (rule braid)+
qed

end

subsection \<open>Coherent morphisms\<close>

definition is_coh :: "('a::cplx \<Rightarrow> 'b::cplx) \<Rightarrow> bool"
  where "is_coh f = (fill \<circ> comp f = comp f \<circ> fill)"

lemma coh_id [simp]: "is_coh id"
  unfolding is_coh_def by fastforce

lemma coh_comp_left_right: "\<lbrakk>is_coh f; is_coh g\<rbrakk> \<Longrightarrow> is_coh (f \<circ> g)"
  unfolding is_coh_def comp_def by metis

lemma coh_comp_left: "is_coh f \<Longrightarrow> is_coh (comp f)"
  unfolding is_coh_def fill_fun comp_def flip_def by metis

lemma coh_comp_right: "is_coh (flip comp f)"
  unfolding is_coh_def fill_fun comp_def flip_def by metis

lemma coh_comp: "is_coh comp"
  unfolding is_coh_def fill_fun comp_def flip_def by metis

lemma coh_const_apply: "is_coh (const x)"
  unfolding is_coh_def comp_def by fastforce

lemma coh_const: "is_coh const"
  unfolding is_coh_def fill_fun flip_def by fastforce

lemma coh_dup: "is_coh dup"
  unfolding is_coh_def comp_def fill_prod by simp

lemma coh_flip: "(\<forall>x. is_coh (f x)) \<longleftrightarrow> is_coh (flip f)"
  unfolding is_coh_def comp_def fill_fun flip_def by metis

lemma coh_join: "is_coh join"
  unfolding is_coh_def fill_fun flip_def by fastforce

lemma coh_swap [simp]: "is_coh prod.swap"
  unfolding is_coh_def fill_prod comp_def by fastforce

lemma coh_fill [simp]: "is_coh fill"
  unfolding is_coh_def fill_fun flip_def by (rule, rule, simp) (rule, rule braid)

lemma coh_curry [simp]: "is_coh curry"
  unfolding is_coh_def fill_fun flip_def by fastforce

lemma coh_uncurry [simp]: "is_coh uncurry"
  unfolding is_coh_def fill_fun flip_def by fastforce

lemma coh_uncurry_left: "is_coh (uncurry f) \<Longrightarrow> is_coh f"
  unfolding is_coh_def fill_fun flip_def
proof (rule; rule; simp; rule)
  fix h :: "\<Lambda> \<Rightarrow> 'a"
  fix d :: \<Delta>
  fix x :: 'b
  let ?h = "\<lambda>l. (h l, x)"
  assume "fill \<circ> comp (uncurry f) = comp (uncurry f) \<circ> fill"
  hence "fill (uncurry f \<circ> ?h) d = uncurry f (fill ?h d)"
    unfolding comp_def by metis
  thus "fill (\<lambda>l. f (h l) x) d = f (fill h d) x"
    unfolding comp_def fill_prod by simp
qed

lemma coh_uncurry_right: "is_coh (uncurry f) \<Longrightarrow> is_coh (flip f)"
  unfolding is_coh_def fill_fun flip_def
proof (rule; rule; simp; rule)
  fix x :: 'a
  fix h :: "\<Lambda> \<Rightarrow> 'b"
  fix d :: \<Delta>
  let ?h = "\<lambda>l. (x, h l)"
  assume "fill \<circ> comp (uncurry f) = comp (uncurry f) \<circ> fill"
  hence "fill (uncurry f \<circ> ?h) d = uncurry f (fill ?h d)"
    unfolding comp_def by metis
  thus "fill (\<lambda>l. f x (h l)) d = f x (fill h d)"
    unfolding comp_def fill_prod by simp
qed

lemma coh_uncurry_left_right: "\<lbrakk>is_coh (flip f); is_coh f\<rbrakk> \<Longrightarrow> is_coh (uncurry f)"
  unfolding  is_coh_def
proof (rule; simp; rule)
  fix h :: "\<Lambda> \<Rightarrow> 'b \<times> 'a"
  fix d :: \<Delta>
  let ?h1 = "fst \<circ> h"
  let ?h2 = "snd \<circ> h"

  assume "fill \<circ> comp f = comp f \<circ> fill"
  hence "\<And>x. fill (f \<circ> ?h1) d x = f (fill ?h1 d) x"
    unfolding comp_def by metis
  hence left: "\<And>x. fill (\<lambda>l. f (?h1 l) x) d = f (fill ?h1 d) x"
    unfolding fill_fun flip_def by simp

  assume "fill \<circ> comp (flip f) = comp (flip f) \<circ> fill"
  hence right: "\<And>x. fill (\<lambda>l. f x (?h2 l)) d = f x (fill ?h2 d)"
    unfolding flip_def comp_def fill_fun by metis

  let ?hh = "\<lambda>l l'. f (?h1 l) (?h2 l')"
  have "fill (uncurry f \<circ> h) d = fill (\<lambda>l. ?hh l l) d"
    unfolding comp_def by simp
  also have "... = fill (\<lambda>l. fill (\<lambda>l'. f (?h1 l) (?h2 l')) d) d" by simp
  also have "... = fill (\<lambda>l. f (?h1 l) (fill ?h2 d)) d"
    using right by simp
  also have "... = f (fill ?h1 d) (fill ?h2 d)"
    using left by simp
  finally show "fill (uncurry f \<circ> h) d = (uncurry f \<circ> fill h) d"
    unfolding fill_prod by simp
qed

lemma coh_uncurry_apply: "is_coh (uncurry f) \<longleftrightarrow> is_coh (flip f) \<and> is_coh f"
  using coh_uncurry_left coh_uncurry_right coh_uncurry_left_right by auto

subsection \<open>Making the subtype defined by coherence predicate into a complex\<close>

typedef (overloaded) ('a::cplx, 'b::cplx) mor = "{f::'a \<Rightarrow> 'b. is_coh f}"
  morphisms raw_mor well_mor
proof
  fix x :: 'b
  show "const x \<in> {f. is_coh f}" unfolding is_coh_def comp_def by simp (metis proj)
qed

type_notation
  mor (infixr "\<rightarrow>" 10)

notation
  raw_mor (infixl "$" 70)

setup_lifting type_definition_mor

lift_definition fill_mor :: "[\<Lambda> \<Rightarrow> 'a::cplx \<rightarrow> 'b::cplx, \<Delta>] \<Rightarrow> 'a \<rightarrow> 'b" is fill
proof -
  fix h :: "[\<Lambda>, 'a] \<Rightarrow> 'b"
  fix d :: \<Delta>
  assume "\<And>x. is_coh (h x)"
  hence "is_coh (flip h)" using coh_flip by auto
  hence "is_coh (fill \<circ> flip h)" using coh_comp_left_right coh_fill by metis
  hence "is_coh (flip (fill h))" unfolding comp_def flip_def fill_fun .
  thus "is_coh (fill h d)" using coh_flip[of "fill h"] by simp
qed

instantiation mor :: (cplx, cplx) cplx
begin

definition fill_mor: "fill = fill_mor"

instance proof
  fix h :: "\<Lambda> \<Rightarrow> 'a \<rightarrow> 'b"
  fix l :: \<Lambda>
  show "fill h (emb l) = h l" unfolding fill_mor by transfer simp
next
  fix f :: "'a \<rightarrow> 'b"
  fix d :: \<Delta>
  show "fill (\<lambda>_. f) d = f" unfolding fill_mor by transfer simp
next
  fix hh :: "[\<Lambda>, \<Lambda>] \<Rightarrow> 'a \<rightarrow> 'b"
  fix d :: \<Delta>
  show "fill (\<lambda>l. fill (hh l) d) d = fill (\<lambda>l. hh l l) d" unfolding fill_mor by transfer simp
next
  fix hh :: "[\<Lambda>, \<Lambda>] \<Rightarrow> 'a \<rightarrow> 'b"
  fix d' d :: \<Delta>
  show "fill (\<lambda>l. fill (hh l) d') d = fill (\<lambda>l. fill (\<lambda>l'. hh l' l) d) d'" unfolding fill_mor
    apply transfer by simp (rule braid)
qed

end

lemma coh_raw_mor: "is_coh raw_mor" unfolding is_coh_def comp_def fill_mor
  apply rule apply rule by transfer simp

lift_definition curry_mor_right :: "('a::cplx \<times> 'b::cplx \<rightarrow> 'c::cplx) \<Rightarrow> 'a \<Rightarrow> 'b \<rightarrow> 'c" is curry
proof -
  fix f :: "'a \<times> 'b \<Rightarrow> 'c"
  fix x :: 'a
  assume "is_coh f"
  hence "is_coh (uncurry (curry f))" by simp
  hence "is_coh (flip (curry f))" by (rule coh_uncurry_right)
  thus "?thesis f x" using coh_flip by fastforce
qed

lift_definition curry_mor :: "('a::cplx \<times> 'b::cplx \<rightarrow> 'c::cplx) \<Rightarrow> 'a \<rightarrow> 'b \<rightarrow> 'c" is curry_mor_right
  unfolding is_coh_def comp_def fill_mor
proof (rule, rule, transfer)
  fix f :: "'a \<times> 'b \<Rightarrow> 'c"
  fix h :: "\<Lambda> \<Rightarrow> 'a"
  fix d :: \<Delta>
  assume "is_coh f"
  hence "is_coh (uncurry (curry f))" by simp
  hence "is_coh (curry f)" by (rule coh_uncurry_left)
  thus "fill (\<lambda>l. curry f (h l)) d = curry f (fill h d)" unfolding is_coh_def comp_def by metis
qed

lift_definition uncurry_mor :: "('a::cplx \<rightarrow> 'b::cplx \<rightarrow> 'c::cplx) \<Rightarrow> 'a \<times> 'b \<rightarrow> 'c"
  is "\<lambda>f. uncurry (raw_mor \<circ> raw_mor f)"
proof (rule coh_uncurry_left_right)
  fix f :: "'a \<rightarrow> 'b \<rightarrow> 'c"
  have "\<And>x. is_coh (raw_mor (f $ x))" using raw_mor by simp
  thus "is_coh (flip (($) \<circ> ($) f))" using coh_flip by fastforce
next
  fix f :: "'a \<rightarrow> 'b \<rightarrow> 'c"
  have "is_coh ($)" by (rule coh_raw_mor)
  moreover have "is_coh (raw_mor f)" using raw_mor by simp
  ultimately show "is_coh (($) \<circ> ($) f)" by (rule coh_comp_left_right)
qed

subsection \<open>How complexes with different base arrows relate\<close>

locale relative =
  fixes incl :: "'\<Gamma> \<Rightarrow> '\<Xi>"
    and monic :: "'\<Gamma> \<Rightarrow> \<Lambda>"
    and epic :: "\<Lambda> \<Rightarrow> '\<Gamma>"
    and bottom :: "'\<Xi> \<Rightarrow> \<Delta>"
  assumes inv [simp]: "epic (monic a) = a"
    and square [simp]: "bottom (incl a) = emb (monic a)"
begin

definition ifill :: "['\<Gamma> \<Rightarrow> 'a, '\<Xi>] \<Rightarrow> 'a::cplx"
  where "ifill h b = fill (h \<circ> epic) (bottom b)"

lemma ifill_sec: "ifill h (incl c) = h c"
  unfolding ifill_def by simp

lemma ifill_proj: "ifill (\<lambda>_. x) b = x"
  unfolding ifill_def comp_def by simp

lemma ifill_diag: "ifill (\<lambda>a. ifill (hh a) b) b = ifill (\<lambda>a. hh a a) b"
  unfolding ifill_def comp_def by simp

lemma ifill_braid: "ifill (\<lambda>a. ifill (hh a) b') b = ifill (\<lambda>a. ifill (\<lambda>a'. hh a' a) b) b'"
  unfolding ifill_def comp_def by (rule braid)

lemma ifill_coh: "is_coh f \<Longrightarrow> ifill \<circ> comp f = comp f \<circ> ifill"
  unfolding is_coh_def ifill_def comp_def by metis

end

subsection \<open>The free model complex generated by an object\<close>

datatype 'a free = From 'a | Fill "\<Lambda> \<Rightarrow> 'a free" \<Delta>

functor map_free by (simp_all add: free.map_id0 free.map_comp comp_def)

inductive cplx_rel :: "['a free, 'a free] \<Rightarrow> bool" where

(* Ensures axioms of a model complex are satisfied *)
cplx_sec [simp]: "cplx_rel (Fill h (emb l)) (h l)" |
cplx_proj [simp]: "cplx_rel (Fill (\<lambda>_. x) d) x" |
cplx_diag [simp]: "cplx_rel (Fill (\<lambda>l. Fill (hh l) d) d) (Fill (\<lambda>l. hh l l) d)" |
cplx_braid [simp]: "cplx_rel (Fill (\<lambda>l. Fill (hh l) d') d) (Fill (\<lambda>l. Fill (\<lambda>l'. hh l' l) d) d')" |

(* Ensures that Fill respects this relation, so the filler on the quotient is well defined *)
cplx_Fill_cong [simp]: "(\<And>l. cplx_rel (h l) (h' l)) \<Longrightarrow> cplx_rel (Fill h d) (Fill h' d)" |

(* Finally, ensures that we indeed have an equivalence relation *)
cplx_refl [simp]: "cplx_rel x x" |
cplx_sym: "cplx_rel x y \<Longrightarrow> cplx_rel y x" |
cplx_trans: "\<lbrakk>cplx_rel x y; cplx_rel y z\<rbrakk> \<Longrightarrow> cplx_rel x z"

quotient_type 'a model = "'a free" / cplx_rel
  morphisms rep_model abs_model
  apply (rule equivpI)
  unfolding reflp_def symp_def transp_def using cplx_refl cplx_sym cplx_trans by auto

lemma abs_model_epic:
  assumes "f \<circ> abs_model = g \<circ> abs_model"
  shows "f = g"
proof
  fix x
  from assms have "\<And>y. f (abs_model y) = g (abs_model y)" unfolding comp_def by metis
  thus "f x = g x" by (metis Quotient_abs_rep Quotient_model)
qed

lift_definition to_model :: "'a \<Rightarrow> 'a model" is From .

lift_definition fill_model :: "[\<Lambda> \<Rightarrow> 'a model, \<Delta>] \<Rightarrow> 'a model" is Fill
  by (rule cplx_Fill_cong)

lemma abs_model_From [simp]: "abs_model (From x) = to_model x"
  by transfer simp

lemma abs_model_Fill [simp]: "abs_model (Fill h d) = fill_model (abs_model \<circ> h) d"
  unfolding comp_def by transfer simp

instantiation model :: (type) cplx
begin

definition fill_model: "fill = fill_model"

instance proof
  fix h :: "\<Lambda> \<Rightarrow> 'a model"
  fix l :: \<Lambda>
  show "fill h (emb l) = h l" unfolding fill_model by transfer simp
next
  fix x :: "'a model"
  fix d :: \<Delta>
  show "fill (\<lambda>_. x) d = x" unfolding fill_model by transfer simp
next
  fix hh :: "[\<Lambda>, \<Lambda>] \<Rightarrow> 'a model"
  fix d :: \<Delta>
  show "fill (\<lambda>l. fill (hh l) d) d = fill (\<lambda>l. hh l l) d" unfolding fill_model by transfer simp
next
  fix hh :: "[\<Lambda>, \<Lambda>] \<Rightarrow> 'a model"
  fix d' d :: \<Delta>
  show "fill (\<lambda>l. fill (hh l) d') d = fill (\<lambda>l. fill (\<lambda>l'. hh l' l) d) d'" unfolding fill_model
    by transfer simp
qed

end

subsection \<open>The operation of taking the free model complex of an object is a monad\<close>

lemma map_free_cong: "cplx_rel x y \<Longrightarrow> cplx_rel (map_free f x) (map_free f y)"
proof (induction x y rule: cplx_rel.induct)
  case (cplx_sec h l)
  then show ?case using cplx_rel.cplx_sec[of "map_free f \<circ> h" l] by simp
next
  case (cplx_proj x d)
  then show ?case by (simp add: comp_def)
next
  case (cplx_diag hh d)
  then show ?case using cplx_rel.cplx_diag[of "\<lambda>l l'. map_free f (hh l l')"] by (simp add: comp_def)
next
  case (cplx_braid hh d' d)
  then show ?case by (simp add: comp_def)
next
  case (cplx_Fill_cong h h' d)
  then show ?case by (simp add: comp_def)
next
  case (cplx_refl x)
  then show ?case by simp
next
  case (cplx_sym x y)
  then show ?case by (simp add: cplx_rel.cplx_sym)
next
  case (cplx_trans x y z)
  then show ?case by (simp add: cplx_rel.cplx_trans[of "map_free f x"])
qed

lift_definition map_model :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a model \<Rightarrow> 'b model" is map_free
  by (rule map_free_cong)

lemma map_model_comp: "map_model (f \<circ> g) = map_model f \<circ> map_model g"
  apply rule by transfer (simp add: free.map_comp)

lemma map_model_id [simp]: "map_model id = id"
  apply rule by transfer (simp add: free.map_id)

functor map_model by (simp_all add: map_model_comp)

lemma map_model_to [simp]: "map_model f (to_model x) = to_model (f x)" by transfer simp
lemma map_model_fill [simp]: "map_model f (fill_model h d) = fill_model (\<lambda>l. map_model f (h l)) d"
  by transfer simp

lemma coh_map_model: "is_coh (map_model f)"
  unfolding is_coh_def fill_model comp_def apply rule apply rule by transfer simp

definition from_free :: "'a::cplx free \<Rightarrow> 'a"
  where "from_free = rec_free id (\<lambda>h. fill (snd \<circ> h))"

lemma from_free_From [simp]: "from_free (From x) = x" unfolding from_free_def by simp

lemma from_free_Fill [simp]: "from_free (Fill h d) = fill (\<lambda>l. from_free (h l)) d"
  unfolding from_free_def comp_def by simp

lemma from_free_cong: "cplx_rel x y \<Longrightarrow> from_free x = from_free y"
proof (induction x y rule: cplx_rel.induct)
  case (cplx_sec h l)
  then show ?case by simp
next
  case (cplx_proj x d)
  then show ?case by simp
next
  case (cplx_diag hh d)
  then show ?case by simp
next
  case (cplx_braid hh d' d)
  then show ?case by simp (rule braid)
next
  case (cplx_Fill_cong h h' d)
  then show ?case by simp
next
  case (cplx_refl x)
  then show ?case by simp
next
  case (cplx_sym x y)
  then show ?case by simp
next
  case (cplx_trans x y z)
  then show ?case by simp
qed

lemma from_free_map: "is_coh f \<Longrightarrow> from_free (map_free f x) = f (from_free x)"
  unfolding is_coh_def comp_def apply (induction x) by simp_all metis

lift_definition from_model :: "'a::cplx model \<Rightarrow> 'a" is from_free
  by (rule from_free_cong)

lemma from_model_to [simp]: "from_model (to_model x) = x" by transfer simp
lemma from_model_fill [simp]: "from_model (fill_model h d) = fill (\<lambda>l. from_model (h l)) d"
  by transfer simp

lemma coh_from_model: "is_coh from_model"
  unfolding is_coh_def fill_model comp_def by transfer simp

lemma from_model_comp_map: "is_coh f \<Longrightarrow> from_model \<circ> map_model f = f \<circ> from_model"
  apply transfer apply rule by simp (rule from_free_map)

abbreviation join_model :: "'a model model \<Rightarrow> 'a model"
  where "join_model \<equiv> from_model"

lemma to_model_natural: "map_model f \<circ> to_model = to_model \<circ> f"
  apply rule by transfer simp

lemma join_model_natural: "join_model \<circ> map_model (map_model f) = map_model f \<circ> join_model"
  by (rule from_model_comp_map) (rule coh_map_model)

lemma from_model_action: "from_model \<circ> map_model from_model = from_model \<circ> join_model"
  by (rule from_model_comp_map) (rule coh_from_model)

lemma join_model_assoc: "join_model \<circ> map_model join_model = join_model \<circ> join_model"
  by (rule from_model_action)

lemma to_left_unit_join: "join_model \<circ> to_model = id"
  by rule simp

lemma from_free_map_to: "from_free (map_free to_model x) = abs_model x"
  by (induction x) (simp_all add: fill_model comp_def)

lemma to_right_unit_join: "join_model \<circ> map_model to_model = id"
proof -
  have "\<And>x. from_free (map_free to_model x) = abs_model x" by (rule from_free_map_to)
  hence "\<And>x. join_model (abs_model (map_free to_model x)) = abs_model x"
    by (simp add: from_model.abs_eq)
  hence "\<And>x. join_model (map_model to_model (abs_model x)) = abs_model x"
    by (simp add: map_model.abs_eq)
  hence "join_model \<circ> map_model to_model \<circ> abs_model = id \<circ> abs_model" unfolding comp_def by auto
  thus ?thesis by (rule abs_model_epic)
qed

subsection \<open>Every model complex is an algebra over this monad and every coherent morphism is a homomorphism between algebras\<close>

term from_model

thm from_model_action

thm from_model_to

thm from_model_comp_map

subsection \<open>Every algebra over this monad is a model complex\<close>

locale model_alg =
  fixes act :: "'a model \<Rightarrow> 'a"
  assumes action [simp]: "act (map_model act m) = act (join_model m)"
  assumes unit [simp]: "act (to_model x) = x"

begin

definition mfill :: "[\<Lambda> \<Rightarrow> 'a, \<Delta>] \<Rightarrow> 'a"
  where "mfill h d = act (fill (to_model \<circ> h) d)"

lemma mfill_sec: "mfill h (emb l) = h l" unfolding mfill_def by simp

lemma mfill_proj: "mfill (\<lambda>_. x) d = x" unfolding mfill_def comp_def by simp

lemma mfill_diag: "mfill (\<lambda>l. mfill (hh l) d) d = mfill (\<lambda>l. hh l l) d"
  unfolding mfill_def comp_def
proof -
  have "act (fill (\<lambda>l. to_model (act (fill (\<lambda>l'. to_model (hh l l')) d))) d) = act (map_model act (fill (\<lambda>l. to_model (fill (\<lambda>l'. to_model (hh l l')) d)) d))"
    unfolding fill_model by simp
  also have "... = act (join_model (fill (\<lambda>l. to_model (fill (\<lambda>l'. to_model (hh l l')) d)) d))"
    by simp
  also have "... = act (fill (\<lambda>l. fill (\<lambda>l'. to_model (hh l l')) d) d)" by (simp add: fill_model)
  also have "... = act (fill (\<lambda>l. to_model (hh l l)) d)" by simp
  finally show "act (fill (\<lambda>l. to_model (act (fill (\<lambda>l'. to_model (hh l l')) d))) d) = act (fill (\<lambda>l. to_model (hh l l)) d)" .
qed

lemma mfill_braid: "mfill (\<lambda>l. mfill (hh l) d') d = mfill (\<lambda>l. mfill (\<lambda>l'. hh l' l) d) d'"
  unfolding mfill_def comp_def
proof -
  have "act (fill (\<lambda>l. to_model (act (fill (\<lambda>l'. to_model (hh l l')) d'))) d) = act (map_model act (fill (\<lambda>l. to_model (fill (\<lambda>l'. to_model (hh l l')) d')) d))"
    unfolding fill_model by simp
  also have "... = act (join_model (fill (\<lambda>l. to_model (fill (\<lambda>l'. to_model (hh l l')) d')) d))"
    by simp
  also have "... = act (fill (\<lambda>l. fill (\<lambda>l'. to_model (hh l l')) d') d)" by (simp add: fill_model)
  also have "... = act (fill (\<lambda>l. fill (\<lambda>l'. to_model (hh l' l)) d) d')"
    apply (rule cong[of act]) by simp (rule braid)
  also have "... = act (join_model (fill (\<lambda>l. to_model (fill (\<lambda>l'. to_model (hh l' l)) d)) d'))"
    by (simp add: fill_model)
  also have "... = act (map_model act (fill (\<lambda>l. to_model (fill (\<lambda>l'. to_model (hh l' l)) d)) d'))"
    by simp
  also have "... = act (fill (\<lambda>l. to_model (act (fill (\<lambda>l'. to_model (hh l' l)) d))) d')"
    unfolding fill_model by simp
  finally show "act (fill (\<lambda>l. to_model (act (fill (\<lambda>l'. to_model (hh l l')) d'))) d) = act (fill (\<lambda>l. to_model (act (fill (\<lambda>l'. to_model (hh l' l)) d))) d')" .
qed

end

end