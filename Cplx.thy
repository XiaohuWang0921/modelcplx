theory Cplx
  imports Main
begin

section \<open>Theory of model complexes\<close>

subsection \<open>Stuff missing from the standard library\<close>

definition flip :: "[['a, 'b] \<Rightarrow> 'c, 'b, 'a] \<Rightarrow> 'c"
  where "flip \<equiv> \<lambda>f x y. f y x"

definition uncurry :: "[['a, 'b] \<Rightarrow> 'c, 'a \<times> 'b] \<Rightarrow> 'c"
  where "uncurry \<equiv> \<lambda>f (x, y). f x y"

definition join :: "[['a, 'a] \<Rightarrow> 'b, 'a] \<Rightarrow> 'b"
  where "join \<equiv> \<lambda>f x. f x x"

definition const :: "['a, 'b] \<Rightarrow> 'a"
  where "const \<equiv> \<lambda>x _. x"

definition dup :: "'a \<Rightarrow> 'a \<times> 'a"
  where "dup \<equiv> \<lambda>x. (x, x)"

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
      and proj [simp]: "fill (\<lambda>_. x) d = x" (* Weakening *)
      and diag [simp]: "fill (\<lambda>l. fill (hh l) d) d = fill (\<lambda>l. hh l l) d" (* Contraction *)
      and braid: "fill (\<lambda>l. fill (hh l) d') d = fill (\<lambda>l. fill (\<lambda>l'. hh l' l) d) d'" (* Permutation *)
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
  show "fill (\<lambda>l. fill (\<lambda>l'. hh l' l) d) d' = fill (\<lambda>l. fill (hh l) d') d"
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
  where "is_coh f \<equiv> fill \<circ> comp f = comp f \<circ> fill"

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

lemma equalizer_of_coh:
  assumes "is_coh f" and "is_coh g" and "\<And>l. f (h l) = g (h l)"
  shows "\<And>d. f (fill h d) = g (fill h d)"
proof -
  fix d :: \<Delta>
  have "f (fill h d) = fill (\<lambda>l. f (h l)) d" using assms(1) unfolding is_coh_def comp_def by metis
  also have "... = fill (\<lambda>l. g (h l)) d" unfolding assms(3) by simp
  also have "... = g (fill h d)" using assms(2) unfolding is_coh_def comp_def by metis
  finally show "?thesis d" .
qed

subsection \<open>Making the subtype defined by coherence predicate into a complex\<close>

lemma fill_coh_is_coh:
  assumes "\<And>l. is_coh (h l)"
  shows "\<And>d. is_coh (fill h d)"
proof -
  fix d :: \<Delta>
  from assms have "is_coh (flip h)" using coh_flip by auto
  hence "is_coh (flip (fill h))"
    using coh_fill coh_comp_left_right unfolding comp_def fill_fun flip_def by fastforce
  thus "?thesis d" using coh_flip by fastforce
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
  where "ifill h b \<equiv> fill (h \<circ> epic) (bottom b)"

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

end