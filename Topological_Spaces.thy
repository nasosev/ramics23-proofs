theory Topological_Spaces
imports Category Orders
begin

locale "open" =
  fixes "open" :: "'a set set"

locale topological_space = "open" +
  fixes universe :: "'a set" 
  assumes open_empty [simp, intro]: "{} \<in> open"
  assumes open_UNIV [simp, intro]: "universe \<in> open"
  assumes open_subsets: "x \<in> open \<Longrightarrow> x \<subseteq> universe"
  assumes open_Int [intro]: "S \<in> open \<Longrightarrow> T \<in> open \<Longrightarrow> (S \<inter> T) \<in> open "
  assumes open_Union [intro]: "\<forall>S\<in>K. S \<in> open \<Longrightarrow> (\<Union>K) \<in> open "

locale finite_topological_space = topological_space + 
  assumes finite_universe[simp]: "finite universe"

locale cover = topological_space + 
  fixes covering :: "'a set set"
  assumes cover_open[simp, intro]: "covering \<subseteq> open"
  assumes covers: "\<Union>(covering) = universe"


definition "lower S \<equiv> {X. \<exists>Y\<in>S. X \<le> Y}"


lemma Sup_is_lower_Sup:"\<Union>S = \<Union>(lower S)"
  apply (clarsimp simp: lower_def)
  apply (safe; clarsimp)
  
   apply blast
  apply blast
  done

term lattice

locale maximal_cover = cover + 
  assumes antichain: "x \<in> covering \<Longrightarrow> y \<in> covering \<Longrightarrow> \<not> (x \<subset> y) "

lemma maximal_in_finite_set: "x \<in> S \<Longrightarrow> P (x :: 'a :: preorder) \<Longrightarrow> finite S \<Longrightarrow> (\<exists>y\<ge>x. y \<in> S \<and>  P y \<and> (\<forall>z\<in>S. P z \<longrightarrow> \<not>(z > y)))" 
  apply (induct S arbitrary: x rule:infinite_finite_induct; clarsimp)
  apply (elim disjE; clarsimp?)
   apply (metis (no_types, lifting) dual_order.refl less_le_not_le order_trans)
  by (metis (full_types) dual_order.strict_trans2 less_le_not_le)

definition "maximal P x \<equiv> P x \<and> (\<forall>y. P y \<longrightarrow> \<not>(y > x))" 

context finite_topological_space
begin

abbreviation (input) "max_cover x \<equiv> maximal_cover open universe x"

definition "cover_join X Y = {Z. Z \<in> X \<union> Y \<and> (\<forall>Z'. Z' \<in> X \<union> Y \<longrightarrow> \<not> Z \<subset> Z')} "

definition "cover_meet X Y = {Z. Z \<in> lower X \<inter> lower Y \<and> (\<forall>Z'. Z' \<in> lower X \<inter> lower Y \<longrightarrow> \<not> Z \<subset> Z')} "

lemma in_cover_is_open: "maximal_cover open universe z \<Longrightarrow> x \<in> z \<Longrightarrow> x \<in> open"
  by (meson cover.cover_open in_mono maximal_cover_def)


lemma spec_set_eq: "X = Y \<Longrightarrow> c \<in> Y \<Longrightarrow> c \<in> X"
  apply (blast)
  done

lemma cover_meet_is_inf: "max_cover A \<Longrightarrow> max_cover B \<Longrightarrow> x \<in> cover_meet A B \<Longrightarrow> (\<exists>y\<in>A.\<exists>z\<in>B. x = y \<inter> z)"
  apply (clarsimp simp: cover_meet_def) 
  apply (clarsimp simp: lower_def)
  by (meson Int_greatest Int_lower1 Int_lower2 order_neq_le_trans)


lemma not_psub_iff:"(\<not> x \<subset> y) \<longleftrightarrow> x = y \<or>  (\<exists>c. c \<in> x \<and> c \<notin> y)" 
  apply (intro iffI)
  apply (safe; clarsimp)
  apply (blast)+
  done

lemma in_univ_in_inter:"maximal_cover open universe A \<Longrightarrow>  maximal_cover open universe B \<Longrightarrow> t \<in> universe \<Longrightarrow> \<exists>U\<in>A. \<exists>V\<in>B. t \<in> U \<inter> V"
  by (metis (mono_tags, opaque_lifting) Int_iff Union_iff cover.covers maximal_cover.axioms(1))


lemma in_univ_in_inter':"maximal_cover open universe A \<Longrightarrow>  maximal_cover open universe B \<Longrightarrow> t \<in> universe \<Longrightarrow> \<forall>U\<in>A. t \<in> U \<longrightarrow> (\<exists>V\<in>B. t \<in> U \<inter> V)" 
  by (metis (mono_tags, opaque_lifting) Int_iff Union_iff cover.covers maximal_cover.axioms(1))

lemma lower_Sup: "lower S = (\<Union>x\<in>S. lower {x})"
  apply (safe; clarsimp simp: lower_def)
  by blast

lemma finite_lower: "finite S \<Longrightarrow> \<forall>x\<in>S. finite x \<Longrightarrow> finite (lower S)"
  apply (subst lower_Sup)
  apply (subst finite_UN; clarsimp)
  by (clarsimp simp: lower_def)

lemma [simp]: "carrier (X \<times> X) = X"
  by (clarsimp simp: carrier_def)

lemma cover_meet_iff: "max_cover a \<Longrightarrow> max_cover b \<Longrightarrow> x \<in> cover_meet a b \<longleftrightarrow> maximal (\<lambda>x. \<exists>U V. U \<in> a \<and> V \<in> b \<and> x \<subseteq> U \<inter> V) x"
  apply (clarsimp simp: cover_meet_def lower_def)
  apply (safe; clarsimp?)
     apply (clarsimp simp: maximal_def)
  apply (intro conjI)
      apply (rule_tac x=xa in exI, intro conjI; clarsimp?)
      apply (rule_tac x=xaa in exI, intro conjI; clarsimp?)
     apply (meson Int_lower1 inf.cobounded2 inf_greatest order_neq_le_trans)
(* 
     apply (clarsimp)
     apply (metis equalityE insert_subsetI psubset_insert_iff)*)
  apply (clarsimp simp: maximal_def)
    apply (blast)
apply (clarsimp simp: maximal_def)
    apply (blast)
  apply (clarsimp simp: maximal_def)
  by (metis Int_iff inf.absorb_iff2 inf_assoc psubsetI)
 

find_consts "'a set \<Rightarrow> 'a set set"

lemma max_cover_closed: "maximal_cover open universe x \<Longrightarrow> maximal_cover open universe y \<Longrightarrow> \<Union> (cover_meet x y) = universe "
apply (safe)[1]
           apply (clarsimp simp: cover_meet_def lower_def )
           apply (subgoal_tac "X=xaa \<inter> xb")
  
            apply (meson in_cover_is_open in_mono open_subsets)
  apply (smt (z3) Int_absorb dual_order.strict_iff_order finite_topological_space.in_cover_is_open finite_topological_space_axioms inf.absorb_iff2 inf.cobounded1 inf.cobounded2 inf_greatest topological_space.open_subsets topological_space_axioms)
          apply (clarsimp)
          apply (clarsimp simp: cover_meet_def)
          apply (frule_tac A=x and B=y in in_univ_in_inter, assumption, assumption)
          apply (clarsimp)
          apply (insert maximal_in_finite_set)[1]
          apply (atomize)
          apply (erule_tac x="U \<inter> xaa" in allE)
          apply (erule_tac x="{x. x \<subseteq> universe}" in allE)
          apply (erule_tac x="\<lambda>v. v \<in> (lower x \<inter> lower y)" in allE)
          apply (drule mp)
           apply (clarsimp)
  apply (meson in_cover_is_open in_mono open_subsets)
          apply (drule mp)
  apply (clarsimp simp: lower_def, intro conjI)
            apply blast
  apply blast
          apply (drule mp)
  apply (clarsimp)
           (* apply (meson finite_UnionD finite_universe open_Union open_subsets rev_finite_subset) *)
          apply (clarsimp)
          apply (rule_tac x=ya in exI; clarsimp)
          apply (intro conjI)
           apply (clarsimp)
           apply (erule_tac x=Z' in allE)
  apply (clarsimp)
           apply (metis Sup_is_lower_Sup Union_upper cover.covers maximal_cover.axioms(1) psubsetI)
  by blast

lemma Int_greatest: "xa \<subseteq> U \<and> xa \<subseteq> V \<longleftrightarrow> xa \<subseteq> (U \<inter> V)"
  by (safe; blast)

lemma maximal_iff: " maximal (\<lambda>xa. \<exists>U. U \<in> x \<and> (\<exists>V. V \<in> y \<and> xa \<subseteq> U \<and> xa \<subseteq> V)) z \<longleftrightarrow> (\<exists>U. U \<in> x \<and> (\<exists>V. V \<in> y \<and> z = U \<inter> V)) \<and> (\<forall>z'. (\<exists>U. U \<in> x \<and> (\<exists>V. V \<in> y \<and> z' \<subseteq> U \<inter> V)) \<longrightarrow> \<not> z \<subset> z')  "
  apply (clarsimp simp: maximal_def)
  apply (intro iffI; clarsimp?)
   apply (metis dual_order.strict_iff_order inf.cobounded2 inf_greatest inf_sup_ord(1))
  by (blast)

lemma maximal_iff': "maximal (\<lambda>xa. \<exists>U. U \<in> x \<and> (\<exists>V. V \<in> y \<and> xa \<subseteq> U \<and> xa \<subseteq> V)) = maximal (\<lambda>v. v \<in> lower x \<inter> lower y)"
  apply (rule ext, safe; clarsimp simp: maximal_def)
   apply (safe; clarsimp simp: lower_def)
     apply (blast)
    apply (blast)
   apply blast
  by (smt (verit, del_insts) lower_def mem_Collect_eq)


(* Max covers are closed under antichain-meet *)
lemma max_cover_closed_meet[simp]:" maximal_cover open universe x \<Longrightarrow> maximal_cover open universe y \<Longrightarrow> maximal_cover open universe (cover_meet x y)"
  apply (standard; clarsimp?)
    apply (clarsimp simp: cover_meet_iff maximal_iff)
    apply (meson in_cover_is_open open_Int)
   apply (erule (1) max_cover_closed)
  apply (clarsimp simp: cover_meet_def lower_def)
  by blast

(* Max covers are closed under antichain-join *)

lemma max_cover_closed_join[simp]:" maximal_cover open universe x \<Longrightarrow> maximal_cover open universe y \<Longrightarrow> maximal_cover open universe (cover_join x y)"
   apply (unfold_locales)[1]
   apply (clarsimp simp: cover_join_def)
   apply (meson in_cover_is_open)
    apply (intro set_eqI iffI; clarsimp)
      apply (clarsimp simp: cover_join_def)
       apply (meson in_cover_is_open in_mono open_subsets)
       apply (clarsimp simp: cover_join_def)
     apply (smt (verit, ccfv_threshold) Int_iff in_univ_in_inter maximal_cover.antichain psubsetD psubset_trans)
    apply (clarsimp simp: cover_join_def)
  by blast

end

end