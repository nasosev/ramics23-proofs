theory Category_Instances
imports Category Orders
begin


definition "mono_rel R \<equiv> \<forall>r\<in>R. \<forall>r'\<in>R. fst r \<le> fst r' \<longrightarrow> snd r \<le> snd r'"

abbreviation inject_delta  ("\<langle>_\<rangle>") where 
"inject_delta (n :: nat) \<equiv> {0..n}"


definition "delta_hom_set  \<equiv> {(n,f, k). single_valued f \<and> mono_rel f \<and> fst ` f = inject_delta n \<and> snd ` f = inject_delta k} "


lemma set_eq_singletonD: "{x} = S \<Longrightarrow> \<forall>y\<in>S. x = y"
  apply (blast)
  done

lemma suc_image: "a ` \<langle>Suc n\<rangle> = (a ` \<langle>n\<rangle>) \<union> {a (Suc n)}"
  apply (safe; clarsimp)
  using le_Suc_eq by auto

lemma card_image: "card (a ` \<langle>n\<rangle>) \<le> (Suc n)"
  apply (induct n, clarsimp)
  apply (clarsimp simp: suc_image)
  by (simp add: card_insert_le_m1)

lemma fun_finite_card: "single_valued r \<Longrightarrow>  card (fst ` r) \<ge> card (snd ` r)"
  apply (case_tac "finite r")
  apply (clarsimp)
  apply (rule card_le_if_inj_on_rel[where r="\<lambda>x y. (x, y) \<in> converse r"], blast)
   apply (metis (no_types, opaque_lifting) converseI imageE image_eqI surjective_pairing)
  apply (drule converseD)+
   apply (erule (2) single_valuedD)
  apply (clarsimp)
  oops

lemma fst_image_singleton:  "fst ` R = S \<Longrightarrow> (converse R) `` (snd ` R) = S " 
  apply (safe, clarsimp simp: image_iff)
   apply (metis fst_eqD)
  apply (clarsimp simp: image_iff Image_iff)
  by (metis  snd_eqD)


lemma helper: "single_valued R \<Longrightarrow> x \<in> (snd ` R) \<Longrightarrow> y \<in> (snd ` R) \<Longrightarrow>  converse R `` {x} \<inter> converse R `` {y} = converse R `` ({x} \<inter> {y}) "
  apply (clarsimp)
  apply (safe, clarsimp simp: Image_iff)
  by (erule (2) single_valuedD)

lemma not_le_natD: "\<not> x \<le> y \<Longrightarrow> y \<le> (x :: nat)"
  by linarith

lemma finite_descent: "finite F \<Longrightarrow> \<not> P {}  \<Longrightarrow> (\<And>F. P F \<Longrightarrow>finite F \<Longrightarrow>  \<exists>F'. F' \<subset> F \<and> P (F')) \<Longrightarrow> \<not> P F"
  apply (clarsimp)
  apply (induct F rule: finite_psubset_induct; clarsimp)
  apply (atomize)
  apply (clarsimp)
  by auto


definition "card_ord S S' \<equiv> \<exists>f. inj_on f S \<and> f ` S \<subseteq> S'"



definition some_elem :: "'a set \<Rightarrow> 'a"
  where "some_elem X = (SOME x. x \<in> X)"

lemma some_elem_eq [simp]: "X \<noteq> {} \<Longrightarrow>some_elem X \<in> X "
  apply (simp add: some_elem_def)
  using some_in_eq by fastforce


find_consts "'a set \<Rightarrow> 'a"

lemma functional_codomain_le_dom:"single_valued R \<Longrightarrow> card_ord (snd ` R) (fst ` R)" 
  apply (clarsimp simp: card_ord_def)
  apply (rule_tac x="\<lambda>x. some_elem (converse R `` {x})" in exI)
  apply (intro conjI)
   apply (rule inj_onI; clarsimp)
  
   apply (metis Image_singleton_iff converseD converseI empty_iff single_valuedD some_elem_eq)
  apply (clarsimp simp: image_iff)
  by (metis Image_singleton_iff converseD converseI empty_iff fst_conv some_elem_eq)


lemma psubset_implies_card_ord: "X \<subseteq> Y \<Longrightarrow> card_ord X Y"
  apply (subst card_ord_def)
  apply (rule_tac x="id" in exI)
  apply (clarsimp)
  done

lemma finite_implies_psubset_not_card_ord: "finite X \<Longrightarrow> card_ord Y X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> X = Y "
  apply (induct X arbitrary: Y rule:finite_induct; clarsimp simp :card_ord_def)
  apply (atomize)
  apply (erule_tac x="Y - {x}" in allE, clarsimp)
  apply (drule mp)
   defer
  apply (drule mp)
    apply (clarsimp)
  apply (blast)
   apply fastforce
  apply (rule_tac x="(\<lambda>v. if f v = x then (f x) else f v)" in exI)
  apply (intro conjI)
   apply (rule inj_onI; clarsimp)
   apply (clarsimp split: if_splits)
     apply (metis inj_on_contraD)
     apply (metis inj_on_contraD)
     apply (metis inj_on_contraD)
   apply (metis inj_on_contraD)
  apply (clarsimp)
  apply (intro conjI) 
   apply (clarsimp)
   apply (metis imageI in_mono inj_on_contraD insertE)
  by blast


locale delta_hom 
begin

sublocale  Hom_Syntax delta_hom_set relcomp done


end

context delta_hom begin

abbreviation "delta_hom \<equiv> hom_of "

lemmas delta_hom_def = hom_of_def 

term "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"

thm delta_hom_set_def

lemma arr_iff: "\<guillemotleft>f : n \<rightarrow> k\<guillemotright> \<longleftrightarrow> single_valued f \<and> mono_rel f \<and> fst ` f = \<langle>n\<rangle> \<and> snd ` f = \<langle>k\<rangle>"
  apply (clarsimp simp: delta_hom_set_def)
  done

lemma delta_hom_le: "n < k \<Longrightarrow> delta_hom n k = {}"
  apply (clarsimp simp: delta_hom_def arr_iff)
  apply (drule functional_codomain_le_dom)
  apply (drule finite_implies_psubset_not_card_ord[rotated])
    apply (clarsimp)+
  done

(*

lemma "single_valued x \<Longrightarrow> mono_rel x \<Longrightarrow> fst ` x = \<langle>k\<rangle> \<Longrightarrow> snd ` x = \<langle>k\<rangle> \<Longrightarrow> (a, b) \<in> x \<Longrightarrow> a \<le> b"
  apply (induct a arbitrary: b; clarsimp)
  apply (atomize)
  oops


lemma delta_hom_eq: "  delta_hom k k = {Id_on \<langle>k\<rangle>  }"
  apply (clarsimp simp: delta_hom_def Id_on_def )
  apply (rule order.antisym)
  apply (induct k; clarsimp)
    apply (safe; clarsimp)
  apply (clarsimp simp: arr_iff)
      apply (metis fst_eqD insert_image singleton_insert_inj_eq')
  apply (clarsimp simp: arr_iff)
     apply (metis snd_eqD insert_image singleton_insert_inj_eq')
    apply (clarsimp simp: arr_iff)

    apply (metis (no_types, opaque_lifting) image_iff prod.exhaust_sel singleton_iff)
  apply (drule_tac c="restrict x {Suc k}" in subsetD)
    apply (clarsimp simp: arr_iff)
    apply (intro conjI; clarsimp?)
       apply (intro single_valuedI; clarsimp simp: restrict_iff)
       apply (meson single_valued_def)
      apply (clarsimp simp: mono_rel_def restrict_iff)
      apply (metis fst_eqD snd_eqD)
     apply (safe; clarsimp simp: restrict_iff)
      apply (metis atLeastAtMost_iff fst_eqD imageI le_SucE)
     apply (clarsimp simp: image_iff restrict_iff Bex_def)
  apply (metis atLeast0AtMost atMost_iff imageE le_Suc_eq prod.exhaust_sel)
    apply (safe; clarsimp simp: restrict_iff)
     defer
     apply (clarsimp simp: image_iff restrict_iff Bex_def)
     defer
     apply (clarsimp simp: arr_iff)
     apply (safe; clarsimp)
  apply (intro conjI)
 
       apply (metis (no_types, lifting) atMost_atLeast0 atMost_iff fst_eqD imageI)
  apply (case_tac "a < Suc k")
       apply (smt (verit, best) UN_E less_SucI not_less_eq old.prod.inject restrict_iff singletonD)
      apply (subgoal_tac "a = Suc k"; clarsimp?)
       apply (rule ccontr)
       apply (metis (no_types, opaque_lifting) atLeastAtMost_iff fst_eqD 
                   imageE imageI le_antisym mono_rel_def snd_eqD)
      apply (metis (no_types, lifting) atMost_atLeast0 atMost_iff 
                      fst_eqD imageI less_Suc_eq_le less_antisym)
  apply (subgoal_tac "xa \<le> k \<or> xa = Suc k", elim disjE ; clarsimp?)
  using restrict_iff apply fastforce
     apply (rule ccontr)
     apply (clarsimp simp: mono_rel_def)
     apply (subgoal_tac "\<exists>v. (Suc k, v) \<in> x")
     apply (subgoal_tac "\<exists>v. (v, Suc k) \<in> x")

      apply (clarsimp)
       apply (erule_tac x="(va, Suc k)" in ballE, clarsimp)
       apply (erule_tac x="(Suc k, v)" in ballE, clarsimp)
  apply (drule mp)
          apply (metis (no_types, opaque_lifting) atLeastAtMost_iff imageI prod.sel(1))
         apply (metis (mono_tags, opaque_lifting) atLeastAtMost_iff atLeastAtMost_singleton 
            imageI prod.sel(2) singletonD)
        apply blast
       apply blast
      apply (drule set_eqD)+
      apply (erule_tac x="Suc k" in allE, fastforce)

      apply (drule set_eqD)+
     apply (erule_tac x="Suc k" in allE, fastforce)
    apply (clarsimp simp: arr_iff)
  apply (intro conjI)
  sledgehammer
  using single_valued_def apply auto[1]
      apply (clarsimp simp: mono_rel_def)
     apply (safe; clarsimp simp: image_iff)
    apply (safe; clarsimp simp: image_iff)
      apply (clarsimp simp: mono_rel_def) 
  oops
 *)

lemma indices_eq: "y \<in> delta_hom k k' \<Longrightarrow> y \<in> delta_hom na ka \<longleftrightarrow> k = na \<and> k' = ka"
  by (clarsimp simp: delta_hom_def arr_iff)

lemma dom_relcomp: "snd ` y \<subseteq> fst ` z \<Longrightarrow> fst ` (y O z) = fst ` y" 
  apply (safe; clarsimp)
   apply (metis fst_conv image_iff)
  apply (clarsimp simp: image_iff Bex_def relcomp.simps)
  by (metis (no_types, lifting) image_iff image_subset_iff prod.collapse snd_conv)

lemma cod_relcomp: "fst ` z \<subseteq> snd ` y \<Longrightarrow> snd ` (y O z) = snd ` z" 
  apply (safe; clarsimp)
   apply (metis snd_conv image_iff)
  apply (clarsimp simp: image_iff Bex_def relcomp.simps)
  by (metis (no_types, lifting) image_iff image_subset_iff prod.collapse fst_conv)

lemma in_hom_iff: "f \<in> delta_hom n k \<longleftrightarrow> \<guillemotleft>f : n \<rightarrow> k \<guillemotright>"
  by (clarsimp simp: delta_hom_def arr_iff)

lemma comp_indices_eq: "y \<in> delta_hom n k \<Longrightarrow> z \<in> delta_hom k k' \<Longrightarrow> 
     y O z \<in> delta_hom a b \<longleftrightarrow>  a = n \<and> b = k'" 
  apply (clarsimp simp: delta_hom_def arr_iff, intro iffI conjI; clarsimp) 
        apply (clarsimp simp add: delta_hom_def dom_relcomp dual_order.refl less_nat_zero_code linorder_not_less)
      apply (simp add: atLeast0AtMost cod_relcomp)
     apply (meson single_valued_relcomp)
    apply (clarsimp simp: mono_rel_def)
    apply (metis fst_conv snd_conv)
   apply (simp add: dom_relcomp)
  apply (simp add: cod_relcomp)
  done

thm comp_indices_eq[simplified in_hom_iff]

lemma Id_on_in_hom_n_n:"Id_on \<langle>n\<rangle> \<in> delta_hom n n"
  apply (clarsimp simp: delta_hom_def arr_iff, intro conjI)
    apply (clarsimp simp: mono_rel_def )
   apply (intro set_eqI iffI; clarsimp simp: Id_on_def image_iff)
  by (intro set_eqI iffI; clarsimp simp: Id_on_def image_iff)


lemma id_on_delta_hom_iff: "Id_on \<langle>n\<rangle> \<in> delta_hom a b \<longleftrightarrow> (a = n \<and> b = n)"
  apply (intro iffI)
  using Id_on_in_hom_n_n indices_eq apply blast
  by ( clarsimp simp: Id_on_in_hom_n_n )

lemma in_hom_le[simp]: "x \<in> delta_hom n k \<Longrightarrow> (a, b) \<in> x \<Longrightarrow> a \<le> n"
  apply (clarsimp simp: delta_hom_def arr_iff)
  by (metis atLeastAtMost_iff fst_eqD imageI)

lemma in_hom_le'[simp]: "x \<in> delta_hom n k \<Longrightarrow> (a, b) \<in> x \<Longrightarrow> b \<le> k"
  apply (clarsimp simp: delta_hom_def arr_iff )
  by (metis atLeastAtMost_iff snd_eqD imageI)

sublocale  unital_magma relcomp "Id_on ` range inject_delta"
  apply (standard; clarsimp)
  oops

lemma id_on_fst [simp, elim]: "(x, y) \<in> f \<Longrightarrow> (x,  x) \<in> Id_on (fst ` f)"
  by (clarsimp simp: Id_on_def, metis fst_conv)


lemma id_on_snd [simp, elim]: "(y, x) \<in> f \<Longrightarrow> (x,  x) \<in> Id_on (snd ` f)"
  by (clarsimp simp: Id_on_def, metis snd_conv)

lemma Id_on_idemp[simp]: "Id_on x O Id_on x = Id_on x" 
  apply (safe; clarsimp)
  apply (intro relcompI)
   apply (blast)+
  done

end

sublocale delta_hom < delta_pre_cat: pre_category "relcomp" delta_hom_set
  apply (standard; (clarsimp simp: id_on_delta_hom_iff arrows_iff )?)
      apply (rule_tac x="(Id_on (fst ` x))" in bexI, clarsimp)
       apply (intro set_eqI iffI; clarsimp)
       apply (rule relcompI[OF id_on_fst]; assumption)
  apply (clarsimp simp: magma.idems_def image_iff Bex_def arrows_iff)
  using Id_on_in_hom_n_n arr_iff hom_of_def apply force
     apply (rule_tac x="(Id_on (snd ` x))" in bexI, clarsimp)

      apply (intro set_eqI iffI; clarsimp)
      apply (rule relcompI[OF _ id_on_snd]; assumption)

  apply (clarsimp simp: magma.idems_def image_iff Bex_def arrows_iff)
  using Id_on_in_hom_n_n arr_iff hom_of_def apply force

    apply (safe; (clarsimp simp: compatible_iff )?)
     apply (clarsimp simp: carrier_def indices_eq[simplified in_hom_iff] comp_indices_eq[simplified in_hom_iff] image_iff)
    apply (clarsimp simp: carrier_def indices_eq[simplified in_hom_iff] comp_indices_eq[simplified in_hom_iff] image_iff)
   apply (clarsimp simp: O_assoc)
  apply (intro conjI)
  using Id_on_in_hom_n_n in_hom_iff apply blast
  using Id_on_in_hom_n_n in_hom_iff apply blast
  done


sublocale delta_hom \<subseteq> delta_cat: category "relcomp" delta_hom_set
  apply (standard; (clarsimp simp: id_on_delta_hom_iff )?)
  apply (rule_tac a="Id_on \<langle>a\<rangle>" in ex1I, clarsimp?)
   apply (intro conjI)
     apply (clarsimp simp: delta_pre_cat.in_units_iff[OF Id_on_in_hom_n_n[simplified in_hom_iff]] )
    apply (rule Id_on_in_hom_n_n[simplified in_hom_iff])
   apply (clarsimp)
   apply (intro conjI; clarsimp)

    apply (intro set_eqI iffI; clarsimp)
  
    apply (metis Id_on_iff delta_hom.arr_iff fst_eqD relcomp.relcompI rev_image_eqI)
   apply (intro set_eqI iffI; clarsimp)
    apply (metis Id_on_iff delta_hom.arr_iff snd_eqD relcomp.relcompI rev_image_eqI)
  apply (clarsimp simp: delta_pre_cat.in_units_iff[OF Id_on_in_hom_n_n[simplified in_hom_iff]] )
  apply (clarsimp simp: delta_pre_cat.a.idems_def)
  apply (clarsimp simp: arrows_def arr_iff)
  apply (safe; clarsimp simp: Id_on_def)
  apply (drule set_eqD)
   apply (metis Id_on_iff Id_on_in_hom_n_n arr_iff id_on_fst in_hom_iff in_hom_le' relcomp.relcompI)
  apply (erule_tac x="Id_on \<langle>a\<rangle>" in allE)
  apply (drule set_eqD)
  apply (clarsimp)
  apply (drule mp)
  
  using Id_on_in_hom_n_n arr_iff in_hom_iff apply auto[1]
  apply (drule mp)
  using Id_on_in_hom_n_n arr_iff in_hom_iff apply auto[1]
  apply (drule set_eqD)
  apply (drule set_eqD)
  apply (drule set_eqD)
  apply (drule set_eqD)
  apply (drule set_eqD)
  apply (clarsimp simp: relcomp.simps)
  by (metis Id_on_iff atLeastAtMost_iff le0)

locale ord_semilattice = poset R + abel_semigroup "carrier R \<times> carrier R" meet "carrier R"
  for R :: "'a rel"  and  meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes 
   meet_le: "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> (meet a b, a) \<in> R" and
   meet_greatest: "(a, b) \<in> R \<Longrightarrow> (a, c) \<in> R \<Longrightarrow>  (a, meet b c) \<in> R" 

lemma [simp]: "sym (X \<times> X)"
  by (clarsimp simp: sym_def)

lemma [intro, simp]:" mono_rel x \<Longrightarrow> mono_rel y \<Longrightarrow> mono_rel (y \<inter> z)"
  by (clarsimp simp: mono_rel_def)

abbreviation "proj f S \<equiv> project f (uminus S)"

lemma proj_iff: "proj f S = f \<inter> (UNIV \<times> S)"
  by (safe; clarsimp simp: project_iff)

definition "to_list f = sorted_list_of_set f"

definition "count f = {(a, b). b \<in> snd ` f \<and> a = card (converse f `` {b})}"

definition "meet_deg_count f g = {(a,b). \<exists>x y. (x,b) \<in> f \<and> (y,b) \<in> g \<and> a = max x y}"  


definition "list_rep xs = {(a,b). xs ! a = b \<and> Suc a \<le> length xs}"

locale list_delta begin


definition "list_delta_hom_set = {(m, xs, n). length xs = Suc m \<and> sorted xs \<and> set xs = \<langle>n\<rangle>}"

definition "map_compose xs ys = map ((!) ys) xs"

notation map_compose (infixl "\<circ>\<^sub>m" 55)

sublocale Hom_Syntax list_delta_hom_set map_compose done


abbreviation "list_delta_hom \<equiv> hom_of"

lemmas list_delta_hom_def = hom_of_def

lemma arr_iff: "\<guillemotleft> xs : n \<rightarrow> k \<guillemotright> \<longleftrightarrow> length xs = Suc n \<and> sorted xs \<and> set xs = \<langle>k\<rangle> "
  by (clarsimp simp: list_delta_hom_set_def)



lemma list_indices_eq[simp]: "y \<in> list_delta_hom k k' \<Longrightarrow> y \<in> list_delta_hom na ka \<longleftrightarrow> k = na \<and> k' = ka"
  by (clarsimp simp: list_delta_hom_def arr_iff)

lemma set_upto_length: "set y = \<langle>n\<rangle> \<Longrightarrow> length y \<ge> n"
  by (metis Suc_le_lessD card_atLeastAtMost card_length diff_zero order_less_imp_le)



lemma sort_sort_append: "sort (x @ sort xs) = sort (x @ xs)"
  apply (induct xs arbitrary: x; clarsimp?)
  apply (clarsimp simp: sort_key_def)
  by (metis sort_key_def sort_key_simps(2) sorted_sort sorted_sort_id)


lemma sort_commute_append: "sort (x @ y) = sort (y @ x)"
  apply (induct x arbitrary: y; clarsimp?)
  apply (clarsimp simp: sort_key_def)
  by (smt (verit, ccfv_threshold) append_Cons fold_append foldr_conv_fold o_apply sort_conv_fold sort_key_simps(2))

lemma mono_sorted: "sorted xs \<Longrightarrow> mono_on  (set xs) f \<Longrightarrow> sorted (map f xs)"
  apply (induct xs; clarsimp)
  apply (intro conjI)
   apply (simp add: mono_onD)
  using mono_on_subset by blast

lemma list_delta_hom_objs_eq: "ys \<in> list_delta_hom n k \<Longrightarrow> xs \<in> list_delta_hom k k' \<Longrightarrow> map (\<lambda>i. xs ! i) ys \<in> list_delta_hom a b \<longleftrightarrow> a = n \<and> b = k'"
  apply (clarsimp simp: list_delta_hom_def arr_iff, safe; clarsimp?)
     apply (metis Icc_eq_Icc atLeastAtMost_upt image_set less_eq_nat.simps(1) map_nth)
  apply (erule mono_sorted)
    apply (metis atLeast0AtMost lessThan_Suc_atMost lessThan_iff mono_on_def sorted_nth_mono)
   apply (metis atLeastAtMost_iff le_imp_less_Suc nth_mem)
  by (metis atLeast0AtMost atLeastAtMost_upt atMost_iff list.set_map map_nth)
 
lemma sorted_list_in[simp]: "sorted_list_of_set \<langle>a\<rangle> \<in> list_delta_hom a a" by (clarsimp simp: list_delta_hom_def arr_iff)

lemma sorted_list_in'[simp]: "\<guillemotleft>sorted_list_of_set \<langle>a\<rangle> :  a \<rightarrow> a\<guillemotright>" by (clarsimp simp: list_delta_hom_def arr_iff)

lemma in_hom_iff: "xs \<in> list_delta_hom n k \<longleftrightarrow> \<guillemotleft>xs : n \<rightarrow> k\<guillemotright>" 
  by (clarsimp simp: hom_of_def)

lemma sorted_list_iff[simp]: "sorted_list_of_set \<langle>a\<rangle> \<in> list_delta_hom x y \<longleftrightarrow> x = y \<and> x = a" 
  apply (safe; clarsimp?)
   apply (simp add: list_delta_hom_def arr_iff)
  apply (simp add: list_delta_hom_def arr_iff)
  done


lemma carrier_iff': "x \<in> carrier {(a, b). \<exists>n k. a \<in> list_delta_hom n k \<and> (\<exists>k'. b \<in> list_delta_hom k k')} \<longleftrightarrow> (\<exists>a b. x \<in> list_delta_hom a b)"
  apply (safe; clarsimp simp: carrier_def image_iff)
   apply (elim disjE; clarsimp)
  apply (erule_tac x="sorted_list_of_set \<langle>a\<rangle>" in allE)
  apply (erule_tac x="a" in allE, clarsimp?)
  done

sublocale list_delta_cat: category map_compose list_delta_hom_set 
  apply (standard; (clarsimp simp: list_delta_hom_objs_eq carrier_iff' compatible_iff sorted_list_iff[simplified in_hom_iff] magma.idems_def arrows_iff)?)
       apply (rule_tac x="sorted_list_of_set \<langle>a\<rangle>" in exI, clarsimp simp: sorted_list_iff[simplified in_hom_iff])
       apply (intro conjI)
  apply (clarsimp simp: map_compose_def)
  
        apply (metis atLeast0AtMost atLeast0LessThan diff_zero length_upt lessThan_Suc_atMost map_nth sorted_list_of_set_range)
       apply (clarsimp simp: arr_iff map_compose_def)
  
       apply (smt (verit, ccfv_SIG) Suc_le_lessD atLeast0AtMost atLeast0LessThan atLeastAtMost_upt atMost_iff card_atLeastAtMost 
         card_length in_set_conv_nth lessThan_Suc_atMost lessThan_iff map_idI map_nth minus_nat.diff_0 nth_map order_le_less_trans
            sorted_list_of_set.length_sorted_key_list_of_set sorted_list_of_set_range)
     
      apply (rule_tac x="(sorted_list_of_set \<langle>b\<rangle>)" in exI, clarsimp simp: sorted_list_iff[simplified in_hom_iff])
      apply (intro conjI)
  apply (clarsimp simp: map_compose_def)
        apply (metis atLeast0AtMost atLeast0LessThan diff_zero length_upt lessThan_Suc_atMost map_nth sorted_list_of_set_range)
       apply (clarsimp simp: arr_iff)
       apply (rule nth_equalityI; clarsimp simp: map_compose_def)


       apply (smt (verit, ccfv_SIG)  Suc_le_lessD atLeast0AtMost atLeast0LessThan atLeastAtMost_upt atMost_iff card_atLeastAtMost 
         card_length in_set_conv_nth lessThan_Suc_atMost lessThan_iff map_idI map_nth minus_nat.diff_0 nth_map order_le_less_trans
            sorted_list_of_set.length_sorted_key_list_of_set sorted_list_of_set_range)
     apply (safe; clarsimp simp: map_compose_def list_delta_hom_objs_eq[simplified in_hom_iff] )
  apply (clarsimp simp: map_compose_def)
    apply (simp add: arr_iff)
  using sorted_list_in' apply blast
  apply (rule_tac a="sorted_list_of_set \<langle>a\<rangle>" in ex1I; clarsimp simp: map_compose_def)
   apply ( intro conjI)
  using sorted_list_in' apply blast
    apply (metis atLeast0AtMost atLeast0LessThan card_lessThan lessThan_Suc_atMost map_nth sorted_list_of_set.length_sorted_key_list_of_set sorted_list_of_set_range)
   apply (intro conjI impI allI; clarsimp)
    apply (metis arr_iff atLeast0AtMost atLeast0LessThan lessThan_Suc_atMost map_nth sorted_list_of_set_range)
   apply (rule nth_equalityI; clarsimp simp: )
   apply (metis (no_types, lifting) arr_iff atLeastAtMost_upt card_atLeastAtMost in_set_conv_nth map_nth minus_nat.diff_0 nth_map nth_mem set_upt sorted_list_of_set.length_sorted_key_list_of_set sorted_list_of_set_range)
   apply (rule nth_equalityI; (clarsimp simp: )?)
  using arr_iff apply blast
  by (metis arr_iff atLeastAtMost_upt map_nth set_upt sorted_list_in' sorted_list_of_set_range)

  

lemma "x \<noteq> 0 \<Longrightarrow>  x = Suc (x - Suc 0)"
  by simp


lemma map_id_l: "map ((!) x) (sorted_list_of_set {..<length x}) = x"
  apply (induct x; clarsimp)
  by (smt (verit, best) Suc_leI atLeast0LessThan butlast_snoc drop_all id_take_nth_drop length_Cons lessI list.discI map_butlast map_is_Nil_conv map_nth sorted_list_of_set_range upt_Suc)

lemma map_id_r:"set x = \<langle>n\<rangle> \<Longrightarrow> map ((!) (sorted_list_of_set (set x))) x = x" 
  apply (induct n arbitrary:x; clarsimp)
   apply (metis map_idI nth_Cons_0 singleton_iff)
  by (smt (verit, best) atLeast0LessThan atLeastAtMost_upt atMost_atLeast0 diff_zero in_set_conv_nth length_upt lessThan_Suc_atMost map_idI map_nth nth_map sorted_list_of_set_range)



sublocale list_delta_op: op_category map_compose list_delta_hom_set  ..

end



end