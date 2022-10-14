theory Information_Algebras
 imports Main "HOL-Library.Multiset" "HOL.Zorn" Orders Category Topological_Spaces Category_Instances
begin






(* Information Algebras a la Kohlas *)

locale quasi_separoid = semilattice +
  fixes indep :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<bottom> _ \<bar> _" 45)
  assumes indep_closed: "indep x y z \<Longrightarrow> (x \<in> S \<and> y \<in> S \<and> z \<in> S)" and
          p1: " indep x y x" and
          p2: " indep x y z \<Longrightarrow> indep y x z" and
          p3: " indep x y z \<Longrightarrow>  w \<preceq> y \<Longrightarrow>  indep x w z" and
          p4: " indep x y z \<Longrightarrow> indep x (times y z) z"

locale pas_morphism = source: semilattice D _ S + target: semigroup D' com \<theta>  
  for D :: "'a rel" and S :: "'a set" and D' :: "'b rel" and  \<theta> :: "'b set"
  and com :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixr "\<oplus>" 50) +
   fixes d :: "'b \<Rightarrow> 'a" 
   assumes source_target: "x \<in> \<theta> \<longleftrightarrow> d x \<in> S"
   assumes hom: "x \<in> \<theta> \<Longrightarrow> y \<in> \<theta> \<Longrightarrow> d (x \<oplus> y) = times (d x) (d y)" 


locale information_algebra = quasi_separoid + pas_morphism + 
  fixes t :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" 
  fixes null :: "'a \<Rightarrow> 'b"
  fixes unit :: "'a \<Rightarrow> 'b"
  assumes null_defined: "x \<in> S \<Longrightarrow> null x \<in> \<theta>"
  assumes unit_defined: "x \<in> S \<Longrightarrow> null x \<in> \<theta>"

  assumes label_null: "x \<in> S \<Longrightarrow> d (null x) = x"
  assumes label_unit: "x \<in> S \<Longrightarrow> d (unit x) = x"
  assumes unit_distrib: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> (unit x \<oplus> unit y) = unit (times x y)"
  assumes null_of: "l \<in> \<theta> \<Longrightarrow> (l \<oplus> (null (d l))) = (null (d l))"  
  assumes unit_of: "l \<in> \<theta> \<Longrightarrow> (l \<oplus> (unit (d l))) = l"  
  assumes t_null_iff: "y \<in> S \<Longrightarrow> l \<in> \<theta> \<Longrightarrow> t y (l) = null y \<longleftrightarrow> l = null (d l)" 
  assumes unit_t: "x \<in> S \<Longrightarrow> l \<in> \<theta> \<Longrightarrow> (l \<oplus> unit x) = t (times (d l) x) l "

  assumes t_source_target: "l \<in> \<theta> \<Longrightarrow> x \<in> S \<Longrightarrow> t x l \<in> \<theta>"
  assumes d_t_inv: "l \<in> \<theta> \<Longrightarrow> x \<in> S \<Longrightarrow> d (t x l) = x"
  assumes d_t_id: "l \<in> \<theta> \<Longrightarrow> t (d l) l = l" 
  assumes transport: "indep (d l) y z \<Longrightarrow>  t y l = t y (t z l)"
  assumes combination: "indep x y z \<Longrightarrow> d l = x \<Longrightarrow> d l' = y \<Longrightarrow> t z (l \<oplus> l') =  ((t z l) \<oplus> (t z l'))" 

begin


lemma t_absorb_le: "y \<preceq> z \<Longrightarrow> l \<in> \<theta> \<Longrightarrow>  t y l = t y (t z l)"
  apply (clarsimp)
  apply (rule transport)
  apply (rule p3[where y=z, rotated])
   apply force
  by (rule p2, rule p1)

end










lemma in_dom_in_rest: "x \<in> fst  ` R \<Longrightarrow> fst ` restrict R {x} \<subset> fst ` R"
  apply (clarsimp simp: image_iff)
  apply (rule; clarsimp simp: image_iff restrict_iff)
    apply force 
  by (drule set_eqD; clarsimp simp: image_iff,
         erule_tac x=x in allE, clarsimp simp: Bex_def restrict_iff)



(*
lemma mono_rel_relcompI[intro]: "mono_rel f \<Longrightarrow> mono_rel g \<Longrightarrow>  mono_rel (f O g)"
  apply (clarsimp simp: mono_rel_def)
  by (metis fst_eqD snd_eqD)
*)
(* 
lemma relcomp_eqD: "h O h' \<in> delta_hom m n \<Longrightarrow> h \<in> delta_hom x y \<Longrightarrow>  (h' \<in> delta_hom y b)  \<Longrightarrow>  x = m \<and> b = n"
  apply (clarsimp simp: delta_hom_def)
  by (simp add: cod_relcomp dom_relcomp)


interpretation Deg: poset "{(f, g). \<exists>m m' h m''. 
   f \<in> delta_hom m n \<and> g \<in> delta_hom m' n \<and> h \<in> delta_hom m'' m' \<and>
    f = relcomp h g}"
  apply (standard; (intro transI refl_onI)?, clarsimp simp: carrier_def )
     apply (rule_tac x=" h O ha" in exI, clarsimp simp: O_assoc)
     apply (clarsimp simp: delta_hom_def)
     apply (intro conjI)
        apply (meson single_valued_relcomp)
       apply (rule mono_rel_relcompI; clarsimp)
      apply (metis dom_relcomp subsetI)
    apply (simp add: cod_relcomp dom_relcomp)
    apply (intro conjI; clarsimp simp: image_iff )
     apply blast
    apply blast
   apply (clarsimp simp: carrier_def image_iff , intro conjI; blast?)
   apply (elim disjE; clarsimp)
    apply (rule_tac x="delta.lid (h)" in exI)
    apply (intro conjI)
     apply (rule_tac x="m" in exI)
  sorry
  using delta.lid_defined[simplified] sledgehammer
  apply (
     apply (clarsimp simp: delta.lid_def)
  thm category.axioms thm delta.category_axioms[THEN category.axioms]
     apply (subst partial_monoid.lid_def)
  thm delta.category_axioms[THEN category.axioms]
  apply (rule delta.category_axioms[THEN category.axioms])
  sledgehammer
  apply (metis (no_types, lifting) Collect_cong case_prod_beta' category.axioms delta_cat_op.op_category_axioms op_category.axioms)
  thm delta.lid_defined
  find_theorems partial_monoid.lid
  using delta.lid_defined sledgehammer
  oops
     apply ( simp only: delta.lid_def, simp )
  apply (simp)
     defer
     apply (subst O_assoc[symmetric])
     apply (subst  delta.lid_id)
  apply (clarsimp simp: carrier_def image_iff, blast )
  find_theorems "partial_monoid.lid"
  sledgehammer
  apply force
  oops
    apply (subst delta.lid_id)
  apply (clarsimp simp: carrier_def)
     apply (metis (mono_tags, lifting) case_prodI fst_eqD image_iff mem_Collect_eq)
    apply (clarsimp)
   apply (rule_tac x="Id_on (fst ` x)" in exI)
   apply (intro conjI)
    apply (rule_tac x="m'" in exI)
  using delta_hom_def delta_hom_eq apply force
   apply (subst delta_cat.l_id; clarsimp simp: carrier_def image_iff)
  apply (subgoal_tac "ha O h = h", subst (asm) O_assoc[symmetric], clarsimp)
  apply (frule (2)  relcomp_eqD)
  apply (clarsimp)
  by (smt (z3) cod_relcomp delta_hom_def delta_hom_eq delta_hom_le dom_relcomp insert_not_empty 
   linorder_not_less mem_Collect_eq mk_disjoint_insert mono_rel_relcompI order_class.order_eq_iff 
relcomp_eqD set_eq_singletonD single_valued_relcomp)

*)








(*
locale simplicial_category =  category "{(a, b). \<exists>n k k'. a \<in> list_delta_hom n k \<and> b \<in> list_delta_hom k k'}" "(\<lambda>xs ys. map (\<lambda>i. ys ! i) xs ) "  "range (sorted_list_of_set o inject_delta)"
*)


lemma fst_Id_on[simp]: "fst ` Id_on obj = obj"
  by (clarsimp simp: Id_on_def, safe; clarsimp simp: image_iff)


lemma snd_Id_on[simp]: "snd ` Id_on obj = obj"
  by (clarsimp simp: Id_on_def, safe; clarsimp simp: image_iff)


definition "set_hom = {(a, f , b). fst ` f \<subseteq> a \<and> snd ` f \<subseteq> b}"

interpretation set_hom: Hom_Syntax set_hom relcomp done

lemma in_hom_iff: "set_hom.in_hom f a b \<longleftrightarrow> f \<subseteq> (a \<times> b)"
  apply (safe; clarsimp simp: set_hom_def)
    apply (metis fst_conv image_subset_iff)
   apply (metis snd_conv image_subset_iff)
  by auto




interpretation unital_magma relcomp set_hom.arrows 
  apply (standard)
  
   apply (rule_tac x="Id_on (fst ` x)" in bexI,  clarsimp simp: delta_hom.Id_on_idemp)
     apply (safe; clarsimp)
    apply (meson delta_hom.id_on_fst relcomp.relcompI)
   apply (clarsimp simp: magma.idems_def delta_hom.Id_on_idemp set_hom.arrows_iff in_hom_iff Id_on_subset_Times)
   apply (rule_tac x="fst ` x" in exI)
   apply (rule_tac x="fst ` x" in exI)
   apply (clarsimp simp: Id_on_subset_Times)
apply (rule_tac x="Id_on (snd ` x)" in bexI,  clarsimp simp: delta_hom.Id_on_idemp)
     apply (safe; clarsimp)
    apply (meson delta_hom.id_on_snd relcomp.relcompI)
   apply (clarsimp simp: magma.idems_def delta_hom.Id_on_idemp set_hom.arrows_iff in_hom_iff Id_on_subset_Times)
   apply (rule_tac x="snd ` x" in exI)
   apply (rule_tac x="snd ` x" in exI)
  apply (clarsimp simp: Id_on_subset_Times)
  done





interpretation set: category relcomp set_hom
  apply (standard; (clarsimp simp:  set_hom.compatible_iff set_hom.arrows_iff in_hom_iff delta_hom.dom_relcomp delta_hom.cod_relcomp)?)
       apply (intro conjI iffI; clarsimp simp: delta_hom.dom_relcomp  delta_hom.cod_relcomp O_assoc set_hom.compatible_iff in_hom_iff)
  
  using SigmaD1 apply blast
  using SigmaD1 apply blast
  using SigmaD1 apply blast
   apply (blast)
  apply (clarsimp simp: idems_def Hom_Syntax.arrows_iff in_hom_iff) 
  apply (rule_tac a="Id_on a" in ex1I, clarsimp simp: delta_hom.Id_on_idemp Id_on_subset_Times )
  apply (safe; clarsimp?)
    apply blast
    apply blast
  apply blast

  apply (clarsimp simp: in_hom_iff) 
  apply (safe; clarsimp simp: Id_on_iff)
  apply (erule_tac x="Id_on a" in allE, clarsimp) 
   apply (smt (z3) Id_on_iff Id_on_subset_Times SigmaD2 relcomp.relcompI subsetD)
  apply (erule_tac x="Id_on a" in allE, clarsimp) 
  using relcomp.cases by blast




locale simplicial_set = list_delta + func "list_delta_op.op.Homset" "set.Homset" "list_delta_op.op.arrow"
                             "set.arrow" 
  

inductive chains_of :: "'a rel \<Rightarrow> 'a list \<Rightarrow> bool" for
  r :: "'a rel"
where cons_step: "chains_of r (x#xs) \<Longrightarrow>  (y, x) \<in> r \<Longrightarrow> chains_of r (y#x#xs) " |
      base[simp]: "  chains_of r  []" |
      single[simp]: "a \<in> carrier r \<Longrightarrow>  chains_of r [a]" 

context proset
begin

definition "proset_hom S = {(a, f, b). f = (a, b) \<and> (a, b) \<in> S}"

definition "trans_rel x y = (fst x, snd y)"

sublocale Hom_Syntax "proset_hom R" trans_rel done

lemma arr_iff: "\<guillemotleft>(a, b) : x \<rightarrow> y\<guillemotright> \<longleftrightarrow> ((a = x) \<and> (y = b) \<and> (a \<preceq> b) )" 
  by (safe; clarsimp simp:  proset_hom_def)

sublocale a: unital_magma  trans_rel  arrows
  by (unfold_locales; clarsimp simp: arrows_iff arr_iff magma.idems_def trans_rel_def, blast)

sublocale category_of: category  trans_rel  "proset_hom R"
  apply (unfold_locales; clarsimp simp: arrows_iff arr_iff Bex_def trans_rel_def compatible_iff)
     apply (meson local.trans_rel transD)
  apply (meson local.trans_rel transD)
    apply (metis local.refl_rel refl_onD refl_onD1)
   apply (meson local.refl_rel refl_onD refl_onD2)
  apply (clarsimp simp:  local.a.idems_def arrows_iff arr_iff trans_rel_def)
  apply (rule_tac a="(a, a)" in ex1I, clarsimp simp: trans_rel_def arr_iff)
  apply (clarsimp simp: arr_iff)
  done

lemma idemp_set: "{x} = {x,x}"
  apply (clarsimp)
  done

lemma all_chains_inhabited: " R \<noteq> {} \<Longrightarrow> {xs. chains_of R xs \<and> length xs = n} \<noteq> {}"
  apply (case_tac n)
   apply (clarsimp)
  apply (subgoal_tac "\<exists>v. v \<in> R", clarsimp)
   apply (rule_tac x="replicate n a" in exI)
  apply (intro conjI)
    apply (induct n; clarsimp)
    apply (atomize)
    apply (case_tac nat; clarsimp)
  apply (rule single)
     apply (meson refl_on_domain refl_rel)
    apply (erule_tac x=a in allE, drule mp, fastforce)
    apply (erule cons_step)
  apply (meson carrier_refl refl_onD1 refl_rel)
   apply (clarsimp)
  apply (fastforce)
  done

definition "nerve_functor r (c :: nat list) = {(a,b). length a = (card (set c)) \<and> chains_of r a \<and>  b = map ((!) a) c  }"


lemma list_nonempty_induct [ case_names single cons]:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x xs. xs \<noteq> [] \<Longrightarrow> P xs \<Longrightarrow> P (x # xs)\<rbrakk> \<Longrightarrow> P xs"
  by(induction xs rule: induct_list012) auto

lemma less_sorted_list: "y \<preceq> hd xs \<Longrightarrow> sorted_wrt (\<preceq>) xs \<Longrightarrow> x \<in> set xs \<Longrightarrow>  xs \<noteq> [] \<Longrightarrow> y \<preceq> x"
  apply (induction xs rule: list_nonempty_induct; clarsimp?)
  by (meson transE trans_rel)

lemma split_nonempty_list: "xs \<noteq> [] \<Longrightarrow> xs = hd xs # tl xs"
  by (clarsimp)

lemma chains_are_sorted_length_n: "chains_of R xs \<longleftrightarrow> sorted_wrt (\<preceq>) xs \<and> set xs \<subseteq> carrier R" 
  apply (intro iffI)
   apply (induction rule: chains_of.induct; clarsimp)
  defer
   
   apply (clarsimp)
   apply (case_tac "xs = []")
  apply (clarsimp)
   apply (induction xs arbitrary: rule: list_nonempty_induct; clarsimp?)
  apply (subst split_nonempty_list) back
    apply (clarsimp)
   apply (rule cons_step)
  apply (clarsimp)
   apply (simp add: list.set_sel(1))
  apply (intro conjI)
   apply (clarsimp)
  apply (rule_tac xs="x#xs" in less_sorted_list; clarsimp)
  by (meson refl_on_domain refl_rel)
  

lemma sorted_wrt_iff_nth_less:
  "\<forall>x\<in>set xs. P x x  \<Longrightarrow> sorted_wrt P xs = (\<forall>i j. i \<le> j \<longrightarrow> j < length xs \<longrightarrow> P (xs ! i) (xs ! j))" 
  apply (induction xs; clarsimp)
  by (auto simp add: in_set_conv_nth Ball_def nth_Cons split: nat.split)


lemma sorted_wrt_sorted_map: "sorted x \<Longrightarrow> sorted_wrt (\<preceq>) a \<Longrightarrow> \<forall>i\<in>set x. i < length a \<Longrightarrow> \<forall>x\<in>set a. x \<preceq> x \<Longrightarrow>  sorted_wrt (\<lambda>x y. a ! x \<preceq> a ! y) x" 
  apply (subst sorted_wrt_iff_nth_less; clarsimp)
  by (metis nat_less_le nth_mem sorted_wrt_nth_less)


interpretation ld: list_delta done

lemma nerve_axiom: "y \<in> ld.list_delta_hom n k \<Longrightarrow> x \<in> ld.list_delta_hom k k' \<Longrightarrow> chains_of R  a \<Longrightarrow> length a = (card (set x)) \<Longrightarrow>  chains_of R  (map ((!) a) x)"
  apply (clarsimp simp: chains_are_sorted_length_n)
  apply (intro conjI)
    apply (clarsimp simp: sorted_wrt_map)
  apply (rule sorted_wrt_sorted_map; clarsimp?)
   apply (clarsimp simp: ld.list_delta_hom_def ld.arr_iff)
     apply (clarsimp simp: ld.list_delta_hom_def ld.arr_iff)
    apply (meson in_mono refl_onD refl_rel)

   apply (clarsimp simp: ld.list_delta_hom_def ld.arr_iff)
  by (simp add: in_mono list_delta.arr_iff list_delta.in_hom_iff)

lemma set_list_delta_iff: "x \<in> ld.list_delta_hom k k' \<Longrightarrow> set x = \<langle>k'\<rangle>"
  apply (clarsimp simp: ld.list_delta_hom_def ld.arr_iff)
  done

lemma op_identity: "ld.list_delta_op.op.identity a = sorted_list_of_set \<langle>a\<rangle>" 
  apply (clarsimp simp: ld.list_delta_op.op.identity_def)
  apply (rule the_equality; clarsimp simp:  arr_iff ld.list_delta_op.idems_def)
   apply (intro conjI)
  apply (clarsimp simp: ld.arr_iff Hom_Syntax.arrows_def image_iff)
    apply (metis ld.arr_iff ld.map_id_r list_delta.map_compose_def list_delta.sorted_list_in')
   apply (safe; clarsimp simp: ld.arr_iff)
    apply (metis ld.map_id_r list_delta.map_compose_def)
   apply (metis atMost_atLeast0 ld.map_id_l lessThan_Suc_atMost list_delta.map_compose_def)
  apply (clarsimp simp: ld.arr_iff Hom_Syntax.arrows_def image_iff)
  by (metis ld.arr_iff ld.map_id_r list_delta.map_compose_def list_delta.sorted_list_in')


lemma set_identity: "set.identity a = Id_on a" 
  apply (clarsimp simp: set.identity_def)
  apply (rule the_equality)
   apply (intro conjI)
     apply (clarsimp simp: idems_def Hom_Syntax.arrows_iff in_hom_iff) 
 apply (clarsimp simp: idems_def Hom_Syntax.arrows_iff in_hom_iff) 
  apply (safe; clarsimp?)
    apply blast
    apply blast
  apply (safe; clarsimp simp: in_hom_iff)
    apply blast
  apply blast
  apply (clarsimp simp: in_hom_iff) 
  apply (safe; clarsimp simp: Id_on_iff)
  apply (erule_tac x="Id_on a" in allE, clarsimp) 
   apply (smt (z3) Id_on_iff Id_on_subset_Times SigmaD2 relcomp.relcompI subsetD)
  apply (erule_tac x="Id_on a" in allE, clarsimp) 
  using relcomp.cases by blast


lemma image_map_length: "length f = Suc b \<Longrightarrow> (!) f ` \<langle>b\<rangle> = set f" 
  by (metis atLeastAtMost_upt list.set_map map_nth)

lemma sub_carrierD[simp]: "S \<subseteq> carrier R \<Longrightarrow> \<forall>x\<in>S. x \<preceq> x"
  
  by (meson in_mono refl_onD refl_rel)


sublocale nerve: simplicial_set "\<lambda>n. {xs. chains_of R xs \<and> length xs = Suc n} " "nerve_functor R"
  apply (unfold_locales)
    apply (clarsimp simp: image_iff ld.arr_iff in_hom_iff)
    apply (clarsimp simp: image_iff nerve_functor_def)
    apply (clarsimp simp: chains_are_sorted_length_n)
    apply (clarsimp simp: sorted_wrt_map)
  apply (intro conjI)
    apply (rule sorted_wrt_sorted_map, assumption+)
    apply (simp add: less_Suc_eq_le)
     apply (clarsimp)
  using image_map_length apply blast
     apply (clarsimp simp: image_iff ld.arr_iff nerve_functor_def ld.map_compose_def)
   apply (intro set_eqI iffI; clarsimp)
  apply (subst map_comp_map[symmetric])
    apply (rule relcompI)
     apply (clarsimp)
     apply (intro conjI)
  apply (simp add: image_map_length)
      apply (rule refl)
     apply (clarsimp)
    apply (clarsimp simp: chains_are_sorted_length_n)
     apply (clarsimp simp: sorted_wrt_map)
  apply (intro conjI)
     apply (rule sorted_wrt_sorted_map, assumption+)
      apply (simp add: less_Suc_eq_le image_map_length, clarsimp) 
  apply (simp add: image_map_length)
    apply (clarsimp simp: chains_are_sorted_length_n)
     apply (metis atLeastAtMost_upt ld.sorted_list_in' length_sorted_list_of_set list.set_map list_delta.arr_iff map_nth)
    apply (clarsimp simp: set_identity op_identity Id_on_def' )
    apply (intro set_eqI iffI; clarsimp simp: nerve_functor_def)
    apply (clarsimp simp: chains_are_sorted_length_n)
  
     apply (metis atLeastAtMost_upt list_delta.arr_iff list_delta.map_id_r list_delta.sorted_list_in' map_nth)
    apply (clarsimp simp: chains_are_sorted_length_n)
  by (metis atLeastAtMost_upt list_delta.arr_iff list_delta.map_id_r list_delta.sorted_list_in' map_nth)





end


definition "apply" (infixr \<open>$\<close> 50) where 
"apply f x = the_elem (f `` {x})" 


definition maps ("_ \<mapsto>_ _" 30)  where
 "maps x f y \<equiv> single_valued f \<and> apply f x = y \<and> x \<in> fst ` f"


definition "lift f = {(x,y). maps (fst x) f (fst y) \<and> maps (snd x) f (snd y)}  "

definition "prosets_hom R R' = {f. lift f `` R = R' \<and> fst ` lift f = R }"

lemma in_lift_iff: "((x, x'), y, y') \<in> lift f \<longleftrightarrow> maps x f y \<and> maps x' f y'"
  by (clarsimp simp: lift_def)


lemma mono_prosets: "f \<in> prosets_hom R R' \<Longrightarrow> maps x f y \<Longrightarrow> maps x' f y' \<Longrightarrow> (x, x') \<in> R \<Longrightarrow> (y, y') \<in> R'"
  apply (clarsimp simp: prosets_hom_def in_lift_iff)
  apply (clarsimp simp: lift_def)
  by blast

lemma in_two_homs: "y \<in> prosets_hom Y Z \<Longrightarrow> y \<in> prosets_hom Y' Z' \<Longrightarrow> Y = Y' \<and> Z = Z'"
  by (clarsimp simp: prosets_hom_def)

lemma fst_lift: "single_valued y \<Longrightarrow> fst ` lift y = fst ` y \<times> fst ` y "
  apply (safe; clarsimp simp: image_iff lift_def )
    apply (simp add: Information_Algebras.maps_def image_iff)
   apply (simp add: Information_Algebras.maps_def image_iff)
  by (metis Information_Algebras.maps_def fst_conv image_eqI)

lemma "lift y `` fst ` lift y = Z"
  apply (clarsimp simp: fst_lift)
  oops

lemma not_in_dom_empty: "x \<notin> fst ` z \<Longrightarrow> z `` {x} = {}"
  apply (safe; clarsimp simp: image_iff)
  apply (metis fst_conv)
  done

lemma apply_relcomp:"single_valued y \<Longrightarrow> single_valued z \<Longrightarrow> x \<in> fst ` z \<Longrightarrow> (y $ z $ x) = (z O y $ x)"
  apply (clarsimp simp: apply_def)
  by (smt (z3) Image_singleton_iff Set.set_insert ex_in_conv insertI1 insert_commute relcomp_Image single_valuedD the_elem_eq)

lemma apply_iff: "single_valued f \<Longrightarrow> (x,y) \<in> f \<Longrightarrow> (f $ x) = y"
  apply (clarsimp simp: apply_def)
  by (metis Image_singleton_iff Set.set_insert ex_in_conv insert_iff single_valuedD the_elem_eq)

lemma split_relcomp: "single_valued y \<Longrightarrow> single_valued z \<Longrightarrow> (a \<mapsto>y O z c) \<longleftrightarrow> (\<exists>b. (maps a y b) \<and> (maps b z c))"
  apply (rule iffI; clarsimp simp: maps_def image_iff)
   apply (intro conjI)
     apply (metis fst_conv)
  apply (clarsimp simp: apply_def)
    apply (smt (z3) Image_singleton_iff Set.set_insert ex_in_conv insertI1 insert_commute relcomp_Image single_valuedD the_elem_eq)
  apply (clarsimp simp: apply_iff)
   apply (metis fst_eqD)
  apply (intro conjI)
  using single_valued_relcomp apply blast
   apply (rule sym, rule apply_relcomp, assumption, assumption)
  apply (clarsimp simp: image_iff)
   apply (metis fst_eqD)
  by (metis apply_iff fst_eqD relcomp.relcompI)
  

lemma lift_relcomp_lift_Image: "single_valued y \<Longrightarrow> single_valued z \<Longrightarrow> lift (y O z) `` x  = lift z `` lift y `` x"
  apply (safe; clarsimp simp: lift_def)
   apply (clarsimp simp: split_relcomp)
   apply (metis fst_conv snd_conv)
  apply (clarsimp simp: split_relcomp)
   apply (metis fst_conv snd_conv)
  done

lemma times_cong: "X = Y \<Longrightarrow>  X \<times> X = Y \<times> Y"
  apply (blast)
  done

lemma preimage_iff[simp]:"(b, a) \<in> f \<Longrightarrow> single_valued f \<Longrightarrow>  (\<exists>x\<in>f. (fst x \<mapsto>f a))"
  by (metis Information_Algebras.maps_def apply_iff fst_conv image_eqI)


lemma domain_relcomp_fun_lift: "fst ` z \<times> fst ` z = lift y `` (fst ` y \<times> fst ` y) \<Longrightarrow>  single_valued y \<Longrightarrow> single_valued z \<Longrightarrow> fst ` (y O z) = fst ` y"
  apply (safe; clarsimp simp: image_iff)
   apply (meson fst_eqD)
  apply (drule set_eqD, clarsimp simp: Image_iff)
  apply (rule_tac x="(a, y O z $ a)" in bexI, clarsimp)
  apply (rule relcompI, assumption)
  apply (clarsimp simp: lift_def)
  apply (erule_tac x=b in allE)
  apply (erule_tac x=b in allE)
  apply (clarsimp)
  by (metis apply_iff relcomp.relcompI single_valued_relcomp)

abbreviation (input) "constrain R S \<equiv> restrict R (uminus S)" 


term set_hom
definition "prosets_hom_set = {(a,f, b). fst f = a \<and> (carrier a, (snd f) , carrier b) \<in> set_hom \<and> fst ` (snd f) = carrier a \<and> proset a \<and> proset b \<and> single_valued (snd f) \<and>   monotone_on (carrier a) (proset.leq a) (proset.leq b) (apply (snd f))}"


interpretation ps: Hom_Syntax prosets_hom_set "\<lambda>x y. (fst x, relcomp (snd x) (snd y))" done


lemma prosets_in_hom_iff: "ps.in_hom f a b \<longleftrightarrow> fst f = a \<and> (carrier a, (snd f) , carrier b) \<in> set_hom \<and> fst ` (snd f) = carrier a \<and> proset a \<and> proset b \<and> single_valued (snd f) \<and>   monotone_on (carrier a) (proset.leq a) (proset.leq b) (apply (snd f))"
  by (clarsimp simp: prosets_hom_set_def)



lemma Collect_iff: "x \<in> Collect P \<longleftrightarrow> P x"
  by (clarsimp)

lemma id_on_maps_id:"(aa \<mapsto>Id_on (fst ` x) ab) \<longleftrightarrow> aa = ab \<and> aa \<in> (fst ` x) "
  apply (safe; clarsimp simp: Id_on_def maps_def)
  using apply_iff apply fastforce
   apply (clarsimp simp: image_iff, metis fst_conv)
  apply (safe)
    apply (rule single_valuedI; clarsimp)
   defer
   apply (clarsimp simp: image_iff, metis fst_conv)
  apply (subgoal_tac "single_valued (\<Union>x\<in>x. {(fst x, fst x)})")
  using apply_iff apply fastforce
  by (rule single_valuedI; clarsimp)

lemma id_on_maps_id':"(aa \<mapsto>Id_on (snd ` x) ab) \<longleftrightarrow> aa = ab \<and> aa \<in> (snd ` x) "
  apply (safe; clarsimp simp: Id_on_def maps_def)
  using apply_iff apply fastforce
   apply (clarsimp simp: image_iff, metis snd_conv)
  apply (safe)
    apply (rule single_valuedI; clarsimp)
   defer
   apply (clarsimp simp: image_iff, metis snd_conv)
  apply (subgoal_tac "single_valued (\<Union>x\<in>x. {(snd x, snd x)})")
  using apply_iff apply fastforce
  by (rule single_valuedI; clarsimp)

lemma Id_on_fst_lid[simp]:"Id_on (fst ` x) O x = x" apply (safe; clarsimp)
  by (meson delta_hom.id_on_fst relcomp.relcompI)


lemma Id_on_snd_lid[simp]:"x O Id_on (snd ` x) = x" apply (safe; clarsimp)
  by (meson delta_hom.id_on_snd relcomp.relcompI)




lemma maps_on_Id: "(x \<mapsto>(Id_on S) y) \<Longrightarrow> x = y \<and> x \<in> S \<and> y \<in> S" 
  apply (clarsimp simp: maps_def)
  using apply_iff 
  by (metis Id_onI single_valued_Id_on)



lemma "single_valued (Id_on S)"
  by (clarsimp simp: single_valued_def)

lemma monotone_Id_on: "monotone_on S R R (apply (Id_on S))"
  apply (clarsimp simp: monotone_on_def)
  apply (subst apply_iff, clarsimp simp: single_valued_Id_on)
   apply (fastforce)
  apply (subst apply_iff, clarsimp simp: single_valued_Id_on)
   apply (fastforce)
  apply (assumption)
  done

lemma in_hom_simp[simp]: "ps.in_hom (a, b) x y \<Longrightarrow> x = a"   by (clarsimp simp: prosets_in_hom_iff)


interpretation prosets: category "\<lambda>x y. (fst x, relcomp (snd x) (snd y))" "prosets_hom_set" 
  apply (standard; (clarsimp simp: delta_hom.dom_relcomp delta_hom.cod_relcomp in_hom_iff ps.arrows_iff  in_two_homs ps.compatible_iff in_hom_simp Collect_iff)?)
       apply (rule_tac x="(a, Id_on (carrier a))" in bexI, clarsimp)
  apply (clarsimp simp: prosets_in_hom_iff)
        apply (metis  set.id_comp_l set_lattice.dual.set_identity)
       apply (clarsimp simp: magma.idems_def ps.arrows_iff )
       apply (intro conjI)
        apply (rule_tac x=" a" in exI)
  apply (rule_tac x=" a" in exI)
        apply (clarsimp simp: prosets_in_hom_iff)
        apply (intro conjI)
         apply (metis set.id_in_hom_l set_lattice.dual.set_identity)
        apply (rule monotone_Id_on)
       apply (rule delta_hom.Id_on_idemp)

      apply (rule_tac x="(ba, Id_on (carrier ba))" in bexI)
  apply (clarsimp simp: prosets_in_hom_iff)
  sledgehammer
        apply (metis prosets_in_hom_iff set.id_comp_r set_lattice.dual.set_identity)
       apply (clarsimp simp: magma.idems_def ps.arrows_iff )
       apply (intro conjI)
        apply (rule_tac x=" ba" in exI)
  apply (rule_tac x=" ba" in exI)
        apply (clarsimp simp: prosets_in_hom_iff)
        apply (intro conjI)
         apply (metis set.id_in_hom_r set_lattice.dual.set_identity)
        apply (rule monotone_Id_on)
      apply (rule delta_hom.Id_on_idemp)
     apply (safe; clarsimp)[1]
      apply (clarsimp simp: prosets_in_hom_iff)
  apply (intro conjI; clarsimp simp: in_hom_iff)
  
         apply blast
  apply (subst delta_hom.dom_relcomp; clarsimp?)
  using prod.collapse apply auto[1]
       apply (erule (1) single_valued_relcomp)
      defer
      defer
      apply (clarsimp simp: O_assoc)
     apply (intro conjI)
      apply (rule_tac x="a" in exI)

      apply (rule_tac x="Id_on (carrier a)" in exI)
        apply (clarsimp simp: prosets_in_hom_iff)

      apply (metis monotone_Id_on set.id_in_hom_l set_lattice.dual.set_identity)
     apply (rule_tac x="ba" in exI)

     apply (rule_tac x="Id_on (carrier ba)" in exI)
        apply (clarsimp simp: prosets_in_hom_iff)

      apply (metis monotone_Id_on set.id_in_hom_r set_lattice.dual.set_identity)
    apply (rule_tac a="(a, Id_on (carrier a))" in ex1I; clarsimp?)
     apply (intro conjI)
       apply (clarsimp simp: prosets_in_hom_iff)
  apply (clarsimp simp: magma.idems_def ps.arrows_iff prosets_in_hom_iff)

       apply (smt (z3) Hom_Syntax.arrows_iff fst_Id_on magma.idems_def mem_Collect_eq monotone_Id_on prosets_in_hom_iff set.id_comp_l set.id_in_hom_l set_lattice.dual.set_identity single_valued_Id_on)
   apply (clarsimp simp: prosets_in_hom_iff)

      apply (metis monotone_Id_on set.id_in_hom_r set_lattice.dual.set_identity)
     apply (clarsimp)
     apply (intro conjI impI)
   apply (clarsimp simp: prosets_in_hom_iff)
   apply (clarsimp simp: prosets_in_hom_iff)

      apply (metis  set.id_comp_l set_lattice.dual.set_identity)
   apply (clarsimp simp: prosets_in_hom_iff)

     apply (metis prosets_in_hom_iff set.id_comp_r set_lattice.dual.set_identity)
    apply (clarsimp simp: magma.idems_def)
  apply (drule set_eqD)
    apply (safe; clarsimp simp: relcomp.simps)
     apply (clarsimp simp: prosets_in_hom_iff)
      apply (clarsimp simp: prosets_in_hom_iff)
   apply (clarsimp simp: prosets_in_hom_iff)


     apply (metis (no_types, lifting) fst_Id_on monotone_Id_on prosets_in_hom_iff set.id_comp_r set.id_in_hom_l set_lattice.dual.set_identity single_valued_Id_on)
    apply (clarsimp simp: prosets_in_hom_iff)
    apply (erule_tac x="a" in allE, erule_tac x="Id_on (carrier a)" in allE, clarsimp)
  apply (metis Id_onI Id_on_fst_lid Id_on_subset_Times in_hom_iff monotone_Id_on)
   apply (rule monotone_onI)
  using apply_relcomp 
   apply (smt (verit) monotone_onD proset.carrier_refl)
    apply (clarsimp simp: prosets_in_hom_iff)
  apply (intro conjI; clarsimp simp: in_hom_iff)
  
         apply blast
  apply (subst delta_hom.dom_relcomp; clarsimp?)
  using prod.collapse apply auto[1]
   apply (erule (1) single_valued_relcomp)
  
   using apply_relcomp monotone_onD proset.carrier_refl  
   by (smt (verit) monotone_on_def)  

 

context proset begin

lemma proset_converse_proset: "proset R \<Longrightarrow> proset (converse R)"
  apply (standard; clarsimp)
   apply (simp add: local.trans_rel)
  by (simp add: carrier_converse_is_carrier local.refl_rel)

end

locale functor_preord_to_preords = source: proset +
 func source.category_of.Homset prosets.Homset source.category_of.arrow "\<lambda>x y. (fst x, relcomp (snd x) (snd y))"

context topological_space begin

sublocale opens_order: poset "{(a,b). a \<in> open \<and> b \<in> open \<and> a \<subseteq> b}"
  apply (unfold_locales; (clarsimp intro: transI)?)
   apply (rule transI; clarsimp)
   apply (blast)
  apply (clarsimp simp :carrier_def, rule refl_onI; clarsimp simp: image_iff)
   apply (blast)
  apply (blast)
  done

sublocale dual_opens_order_category: op_category opens_order.category_of.arrow opens_order.category_of.Homset ..

sublocale opens_dual_order: poset "converse {(a,b). a \<in> open \<and> b \<in> open \<and> a \<subseteq> b}"
  apply (unfold_locales; (clarsimp intro: transI)?)
   apply (rule transI; clarsimp)
   apply (blast)
  apply (clarsimp simp :carrier_def, rule refl_onI; clarsimp simp: image_iff)
   apply (blast)
  apply (blast)
  done

end


type_synonym ('a, 'val) profun = "(('a \<times> 'val) set \<times> ('a \<times> 'val) set) set"


definition "mapf (f :: ('a \<times> 'b) set) = {(xs, ys). set xs \<subseteq> fst ` f \<and> ys = map (apply f) xs}"

definition "nerve_obj R n = {xs. chains_of R xs \<and> length xs = n} "

definition "nondegen S = {x. x \<in> S \<and> distinct_adj x}"


definition "chaos_obj R = \<Union>(nondegen ` range (nerve_obj R))"

definition "chaos_fun (f :: ('a, 'val) profun) = mapf f O to_rel (remdups_adj)  "


(* definition "nerve_fun R (f :: ('a, 'val) profun) (g :: nat list) = (nerve_functor R g) O mapf f" *)

term simplicial_set

locale presheaf = source: op_category + func "source.op.Homset" "set.Homset" "source.op.arrow"
                             "set.arrow" 



locale Omega = topological_space + 
  fixes \<omega> :: "'a \<Rightarrow> 'val rel"
  assumes omega_to_preord: "x \<in> universe \<Longrightarrow> proset (\<omega> x)" 
begin

definition "\<Omega> S = {(s :: ('a \<times> 'val) set, s'). single_valued s \<and> single_valued s' \<and>
                   fst ` s = fst ` s' \<and> (\<forall>v \<in> s. \<exists>val'. (fst v, val') \<in> s' \<and> 
                                                (fst v, snd v, val') \<in> Sigma S \<omega>)}"



lemma trans_omega: "S \<in> open \<Longrightarrow> trans (\<Omega> S)"
  apply (rule transI)
  apply (clarsimp simp: \<Omega>_def)
  apply (erule_tac x="(a,b)" in ballE; clarsimp)
  apply (erule_tac x="(a,val')" in ballE; clarsimp) 
  apply (rule_tac x="val'a" in exI)
  apply (clarsimp)
  apply (subgoal_tac "trans (\<omega> a)")

   apply (meson transD)
  apply (subgoal_tac "a \<in> universe")
  using omega_to_preord proset.axioms(1) transitive_def apply blast
  using open_subsets by fastforce


lemma om_iff: "(x, y) \<in> \<Omega> s \<longleftrightarrow> single_valued x \<and> single_valued y \<and>  fst ` x = fst ` y \<and> (\<forall>v \<in> x. \<exists>val'. (fst v, val') \<in> y \<and> (fst v, snd v, val') \<in> Sigma s \<omega>)  "
  by (clarsimp simp: \<Omega>_def; safe; clarsimp)



lemma is_proset: "S \<in> open \<Longrightarrow> proset (\<Omega> S)"
  apply (standard, erule trans_omega)
  apply (clarsimp simp: refl_on_def) 
  apply (intro conjI)
  apply (clarsimp simp: carrier_def, safe)
    apply (meson Id_on_iff delta_hom.id_on_fst)
   apply (meson Id_on_iff delta_hom.id_on_snd)
  thm opens_order.carrier_refl
  apply (clarsimp simp: om_iff opens_order.carrier_refl)
  apply (intro conjI)
  apply (clarsimp simp: carrier_def)
  apply (clarsimp simp:  image_iff )
   apply (clarsimp simp: \<Omega>_def)
   apply (blast)

  apply (clarsimp simp: carrier_def)
  apply (clarsimp simp:  image_iff )
  apply (elim disjE)
   apply (clarsimp simp: om_iff)
  
   apply (rule_tac x="b" in exI; clarsimp)
   apply (intro conjI)
    apply (erule_tac x="(a,b)" in ballE; clarsimp)
  apply (erule_tac x="(a,b)" in ballE; clarsimp)
  using omega_to_preord 
   apply (meson in_mono open_subsets proset.refl_rel refl_onD refl_on_domain)
  apply (clarsimp simp: om_iff)
  apply (rule_tac x="ba $ a" in exI)
  (* smt timing out, fix later *)
proof -
  fix a :: 'a and b :: 'val and aa :: "('a \<times> 'val) set" and ba :: "('a \<times> 'val) set"
  assume a1: "\<forall>v\<in>aa. \<exists>val'. (fst v, val') \<in> ba \<and> fst v \<in> S \<and> (snd v, val') \<in> \<omega> (fst v)"
  assume a2: "(a, b) \<in> ba"
  assume a3: "fst ` aa = fst ` ba"
  assume a4: "S \<in> open"
  assume a5: "single_valued ba"
  obtain pp :: "('a \<times> 'val) set \<Rightarrow> ('a \<times> 'val \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'val" where
    "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 \<in> x0) = (x2 = x1 (pp x0 x1 x2) \<and> pp x0 x1 x2 \<in> x0)"
    by moura
  then have f6: "a = fst (pp aa fst a) \<and> pp aa fst a \<in> aa"
    using a3 a2 by (metis (no_types) fst_conv imageE image_eqI)
  then have "(snd (pp aa fst a), b) \<in> \<omega> a"
    using a5 a2 a1 by (metis apply_iff)
  then have "(b, b) \<in> \<omega> a"
    using f6 a4 a1 by (metis omega_to_preord open_subsets proset.refl_rel refl_onD refl_on_domain subsetD)
  then show "(a, ba $ a) \<in> ba \<and> a \<in> S \<and> (b, ba $ a) \<in> \<omega> a"
    using f6 a5 a2 a1 by (metis (no_types) apply_iff)
qed
 (*  by (smt (verit) apply_iff fst_conv image_iff in_mono omega_to_preord open_subsets proset.refl_rel refl_onD refl_on_domain) *)


definition "rest (c :: 'a set \<times> 'a set) = {(a,b).  a \<in> (carrier (\<Omega> (snd c))) \<and> b = restrict a (uminus (fst c))}"



lemma sub_productI: "fst ` R \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<in> fst ` R \<Longrightarrow> R `` {x} \<subseteq> B) \<Longrightarrow> R \<subseteq> A \<times> B"
  by (smt (verit, ccfv_threshold) Image_singleton_iff SigmaE mem_Sigma_iff subsetD subsetI subset_fst_snd)



lemma in_open_in_univ: "x \<in> s \<Longrightarrow> s \<in> open \<Longrightarrow> x \<in> universe"
  by (meson in_mono open_subsets)

lemma proset_carrier_iff: "proset s \<Longrightarrow> x \<in> carrier s \<longleftrightarrow> (x, x) \<in> s"
  apply (clarsimp simp: carrier_def, safe; clarsimp?)
    apply (meson proset.refl_rel refl_onD refl_on_domain)
  apply (meson proset.refl_rel refl_onD refl_on_domain)
  by (metis image_iff fst_conv )

lemma carrier_om_iff: "s \<in> open \<Longrightarrow>  x \<in> carrier (\<Omega> s) \<longleftrightarrow> (fst ` x \<subseteq> s \<and> single_valued x \<and> (\<forall>v\<in>x. snd v \<in> carrier (\<omega> (fst v))))" 
  apply (subst proset_carrier_iff, erule is_proset, rule iffI )
  apply (clarsimp simp: om_iff carrier_def, safe; clarsimp simp: om_iff image_iff)
        apply fastforce
   apply (metis fst_conv snd_conv)
  apply (clarsimp)
  apply (subst (asm) ball_cong[OF refl proset_carrier_iff])
  using in_open_in_univ omega_to_preord apply auto[1]
  
  apply (clarsimp simp: om_iff carrier_def)
  apply (rule_tac x=b in exI)
  by auto
 

lemma single_valued_restrictI: "single_valued R \<Longrightarrow> single_valued (restrict R S)"
  by (clarsimp simp: single_valued_def restrict_def)

lemma fst_restrict[simp]: "fst ` restrict R S = (fst ` R) - S"
  apply (clarsimp simp: restrict_def, safe; clarsimp simp: Bex_def image_iff)
  by (blast)

lemma dom_constrained[simp]: "fst ` (constrain R S) \<subseteq> S"
  by (safe; clarsimp simp: restrict_def)

lemma restrict_subset: "S \<subseteq> S' \<Longrightarrow> restrict R (- S) = restrict (restrict R (- S')) (- S)"
  apply (clarsimp simp: restrict_def, safe; clarsimp)
  by blast

lemma apply_rest: " x \<in> carrier (\<Omega> b) \<Longrightarrow> (rest (a, b) $ x) = constrain x a"
  apply (subst apply_iff)
    defer
    defer
    apply (rule refl)
   apply (clarsimp simp: rest_def)
   apply (simp add: single_valued_def)
  by (clarsimp simp: rest_def)

lemma fst_collect_pair: "fst ` {(x, y). P x y} = {x. \<exists>y. P x y}"
  apply (safe; clarsimp)
   apply (fastforce)
  apply (clarsimp simp: image_iff)
  apply (fastforce)
  done


lemma opens_identity[simp]:"a \<in> open \<Longrightarrow> dual_opens_order_category.op.identity a = (a, a)"
  apply (clarsimp simp: dual_opens_order_category.op.identity_def, rule the_equality)
   apply (safe; (clarsimp simp: opens_order.arr_iff magma.idems_def opens_order.trans_rel_def)?)
  using dual_opens_order_category.opHom.arrows_iff opens_order.arr_iff apply auto[1]
  by (clarsimp simp: opens_order.arr_iff) 

term "rest (a,a)"

lemma rest_id_on:"a \<in> open \<Longrightarrow> rest (a, a) = Id_on (carrier (\<Omega> a))"
  apply (safe; clarsimp simp: Id_on_def)
   apply (clarsimp simp: rest_def)
   apply (safe; clarsimp simp: restrict_def)
   apply (clarsimp simp: carrier_om_iff)
   apply auto[1]
  apply (clarsimp simp: rest_def)
  apply (clarsimp simp: carrier_om_iff)
   apply (safe; clarsimp simp: restrict_def)
  by auto


lemma prosets_identity: "proset a \<Longrightarrow> prosets.identity a = (a, Id_on (carrier a))"
  apply (clarsimp simp: prosets.identity_def, rule the_equality)
  apply (safe; (clarsimp simp: prosets_in_hom_iff in_hom_iff)?)
      apply (simp add: Id_on_subset_Times monotone_Id_on)
     apply (clarsimp simp: prosets.a.idems_def)
     apply (intro conjI)
 apply (clarsimp simp: magma.idems_def ps.arrows_iff )
        apply (rule_tac x=" a" in exI)
  apply (rule_tac x=" a" in exI)
        apply (clarsimp simp: prosets_in_hom_iff)
      apply (intro conjI)
       apply (simp add: Id_on_subset_Times in_hom_iff)
  using monotone_Id_on apply blast
        apply (rule delta_hom.Id_on_idemp)
  
    apply blast
   apply blast
  apply (clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: prosets_in_hom_iff)
   apply (clarsimp simp: prosets_in_hom_iff)
  by (metis (no_types, lifting) fst_Id_on monotone_Id_on 
 set.id_comp_r set.id_in_hom_l set_lattice.dual.set_identity single_valued_Id_on)
 
 

sublocale omega: contravariant_func opens_order.category_of.Homset  opens_order.category_of.arrow  "prosets.Homset" "prosets.arrow" \<Omega> "\<lambda>(x,y). (\<Omega> y, rest (x, y)) "
  apply (standard)
    apply (clarsimp simp: opens_order.arr_iff prosets_in_hom_iff in_hom_iff)
    apply (intro conjI)
        apply (rule sub_productI)
       apply (clarsimp simp: rest_def carrier_om_iff om_iff restrict_iff Ball_def single_valued_restrictI)  

  apply (clarsimp simp: image_iff restrict_iff)
         apply (clarsimp simp: rest_def carrier_om_iff om_iff restrict_iff Ball_def single_valued_restrictI)  
  apply (clarsimp simp: rest_def fst_collect_pair)
      apply (clarsimp simp: is_proset)
  apply (clarsimp simp: is_proset)
     apply (clarsimp simp: rest_def single_valued_def)
    apply (rule monotone_onI)
  apply (clarsimp simp: apply_rest)

       apply (clarsimp simp: rest_def carrier_om_iff om_iff restrict_iff Ball_def single_valued_restrictI)  

    apply meson
  apply (clarsimp split: prod.splits)
   apply (clarsimp simp: opens_dual_order.arr_iff prosets_in_hom_iff in_hom_iff opens_dual_order.trans_rel_def rest_def)
   apply (safe; clarsimp simp: relcomp.simps rest_def)
  apply (intro conjI)

  apply (smt (verit) Diff_iff carrier_om_iff case_prod_conv dom_constrained mem_Collect_eq opens_order.arr_iff restrict_def single_valued_restrictI)
     apply (simp add: opens_order.arr_iff restrict_subset)
  
  apply (simp add: restrict_iff)
   apply (metis (no_types, lifting) case_prodD mem_Collect_eq opens_order.proset_axioms proset.arr_iff restrict_subset)
  apply (clarsimp simp: opens_order.arr_iff )

  by (clarsimp simp: prosets_identity is_proset rest_id_on)



sublocale Hom_Syntax "opens_order.category_of.Homset" "opens_order.category_of.arrow" done


lemma dom_rest: "fst ` rest (a, b) =  (carrier (\<Omega> b))"
  by (safe; clarsimp simp: rest_def image_iff)

lemma single_valued_Image_singleton_iff: "single_valued f \<Longrightarrow> R \<inter> (fst ` f) \<noteq> {} \<Longrightarrow> f `` R = {x} \<longleftrightarrow> (\<forall>y\<in>(R \<inter> (fst ` f)). (y, x) \<in> f) " 
  apply (intro iffI) 
  apply (safe; clarsimp simp: single_valued_def Image_iff)
   apply (drule set_eqD, clarsimp simp: Image_iff)
   apply auto[1]
  apply (intro set_eqI iffI; clarsimp simp: Image_iff)
   apply (metis Id_on_iff Int_iff delta_hom.id_on_fst single_valued_def)
  by blast
  

lemma apply_in_fst_in_snd: "single_valued f \<Longrightarrow> x \<in> fst ` f \<Longrightarrow> (f $ x) \<in> snd ` f"
  apply (clarsimp simp: apply_def Image_iff image_iff the_elem_def)
  apply (rule the1I2)
   apply (rule_tac a=b in ex1I, subst single_valued_Image_singleton_iff; (clarsimp simp: image_iff)?)
    apply (clarsimp simp: Bex_def, blast)
   apply force
  apply force
  done
  

lemma mapf_relcomp_distrib: "fst ` (f O g) = fst ` f \<Longrightarrow> snd ` f \<subseteq> fst ` g \<Longrightarrow> single_valued f \<Longrightarrow> single_valued g \<Longrightarrow>  mapf (f O g) = mapf f O mapf g"
  apply (safe; clarsimp simp: mapf_def relcomp.simps)
   apply (intro conjI; clarsimp?)
    apply (clarsimp simp: image_iff )
    apply (meson apply_in_fst_in_snd imageE subsetD)
  apply (subst apply_relcomp; clarsimp)
   apply fastforce
  apply (subst apply_relcomp; clarsimp)
  apply (blast)
  done


lemma mapf_relcomp_distrib': "set_hom.in_hom f a b \<Longrightarrow> set_hom.in_hom g b c \<Longrightarrow> single_valued f \<Longrightarrow> single_valued g \<Longrightarrow>  mapf (f O g) = mapf f O mapf g"
  apply (safe; clarsimp simp: mapf_def relcomp.simps in_hom_iff)
   apply (intro conjI; clarsimp?)
  
  using image_iff apply fastforce
    apply (clarsimp simp: image_iff )
  using apply_in_fst_in_snd 
  apply (smt (verit, del_insts) apply_iff fst_conv image_iff relcompE subsetD)
 
   apply (subst apply_relcomp; clarsimp)
  using image_iff apply fastforce
  apply (intro conjI)
   apply (clarsimp)
    apply (clarsimp simp: image_iff Bex_def relcomp.simps )


   apply (smt (verit, ccfv_SIG) apply_iff image_iff prod.exhaust_sel subsetD)
  apply (clarsimp)
  apply (subst apply_relcomp; clarsimp) 
  using image_iff apply fastforce
  done


lemma remdups_adj_map_remdups:"remdups_adj (map (g o f) xs) = remdups_adj (map g (remdups_adj (map f xs)))" 
  apply (induct xs; clarsimp)
  apply (case_tac "xs"; clarsimp)
  apply (intro conjI impI)
   apply (smt (verit) list.simps(9) remdups_adj.simps(3) remdups_adj_Cons_alt)
  by (smt (verit) hd_remdups_adj list.discI list.sel(1) list.sel(3) remdups_adj.elims)


lemma chaos_relcomp_distrib: "set_hom.in_hom f a b \<Longrightarrow> set_hom.in_hom g b c \<Longrightarrow> single_valued f \<Longrightarrow> single_valued g  \<Longrightarrow> chaos_fun (f O g) = chaos_fun f  O chaos_fun g" 
  apply (clarsimp simp: chaos_fun_def, safe; clarsimp simp: relcomp.simps)
   apply (subst (asm) mapf_relcomp_distrib', assumption+ )
  apply (clarsimp simp: relcomp.simps)

   apply (intro exI, rule conjI)
    apply (rule exI, erule conjI)
  apply (rule refl)

   apply (clarsimp simp: mapf_def)
   apply (subst remdups_adj_map_remdups)
   apply (clarsimp)
  apply (subst mapf_relcomp_distrib'; clarsimp?)
  apply (assumption)+

  apply (clarsimp simp: relcomp.simps) 
  apply (rule_tac x=" map (apply g) ya " in exI)
  apply (intro conjI)
  apply (rule exI, erule conjI)
   apply (clarsimp simp: mapf_def)
    apply (clarsimp simp: mapf_def) 
  by (simp add: remdups_adj_map_remdups)


lemma mapf_iff: "(x, y) \<in> mapf f \<longleftrightarrow> map (apply f) x = y \<and> set x \<subseteq> fst ` f"
  apply (safe; clarsimp simp: mapf_def)
  apply (blast)
  done

lemma subset_product_iff: "x \<subseteq> a \<times> b \<longleftrightarrow> fst ` x \<subseteq> a \<and> snd ` x \<subseteq> b"
  apply (safe; clarsimp)
     apply (fastforce)+
  done


lemma redumps_adj_in_chaos_iff:"proset b \<Longrightarrow> remdups_adj y \<in> chaos_obj b \<longleftrightarrow> (set y \<subseteq> carrier b \<and> sorted_wrt (\<lambda>x y. (x, y) \<in> b) y)" 
  apply (safe)
   apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def proset.chains_are_sorted_length_n)
    apply (blast)
   apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def)
   apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def proset.chains_are_sorted_length_n)
   apply (induct y, clarsimp)
   apply (clarsimp)
   apply (case_tac y; clarsimp split: if_splits)
   apply (meson proset_carrier_iff)
  apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def proset.chains_are_sorted_length_n)
  apply (induct y; clarsimp)
  
  by (smt (verit) list.sel(1) list.sel(3) remdups_adj.elims remdups_adj_set sorted_wrt.elims(3))

lemma cod_restrictD: "snd ` restrict R (- a) \<subseteq> b \<Longrightarrow> \<forall>x\<in>a. R `` {x} \<subseteq> b"
  apply (safe; clarsimp simp: restrict_def)
  by auto

lemma "single_valued f \<Longrightarrow> x \<in>fst ` f \<Longrightarrow> f `` {x} = {f $ x}" 
  apply (clarsimp simp: image_iff apply_iff)
  using single_valued_def by fastforce

definition "source f = (THE a. \<exists>b. ps.in_hom f a b)"

definition "target f = (THE b. \<exists>a. ps.in_hom f a b)"

term chaos_obj

term Hom_Syntax.targets

definition "chaos_fun' f = {(x,y). x \<in> chaos_obj (fst f) \<and> (x,y) \<in> chaos_fun (snd f)}" 

lemma source_iff: "ps.in_hom f a b \<Longrightarrow> source f = a"   
  apply (clarsimp simp: source_def, rule the_equality, fastforce)
  apply (clarsimp)
  apply (clarsimp simp: prosets_in_hom_iff)
  oops


(* lemma chains_of_length_id: "proset b \<Longrightarrow> (\<exists>x. chains_of b x xs) \<longleftrightarrow> chains_of b (length xs) xs"
  apply (safe; (clarsimp simp: proset.chains_are_sorted_length_n ))
  done

lemma chains_of_length: "proset b \<Longrightarrow> chains_of b n xs \<Longrightarrow> chains_of b (length xs) xs"
  apply (subst chains_of_length_id[symmetric]; clarsimp?)
  apply (fastforce)
  done *)

lemma ex_eq: "(\<exists>b. P b \<and> b = a) \<longleftrightarrow> P a"
  by (safe; clarsimp)



lemma chains_of_remdups: "chains_of R  (xs) \<Longrightarrow>   chains_of R (remdups_adj xs)" 
  apply (induction arbitrary: rule:chains_of.inducts; clarsimp?)
  by (metis cons_step remdups_adj_Cons_alt)



lemma ps_in_hom_set_hom: "ps.in_hom f a b \<Longrightarrow> set_hom.in_hom (snd f) (carrier a) (carrier b)"
  by (clarsimp simp: prosets_in_hom_iff)

lemma chains_of_remdups_chaos: "chains_of b  y \<Longrightarrow>  remdups_adj y \<in> chaos_obj b"
  apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def)
  by (erule chains_of_remdups)



lemma mapf_cons: "single_valued f \<Longrightarrow> (a # list, b # list') \<in> mapf f \<longleftrightarrow> ((maps a f b) \<and> (list, list') \<in> mapf f)"
  apply (safe; clarsimp simp: mapf_def maps_def)
  done

lemma monotone_map_betw_chains: "ps.in_hom f a b \<Longrightarrow> (x, y) \<in> mapf (snd f) \<Longrightarrow> sorted_wrt (proset.leq a) x  \<Longrightarrow> y \<in> \<Union> (range (nerve_obj b))"
  apply (clarsimp simp: proset.chains_are_sorted_length_n sorted_wrt_map nerve_obj_def)
  apply (subst proset.chains_are_sorted_length_n)
   apply (clarsimp simp: prosets_in_hom_iff in_hom_iff mapf_def nerve_obj_def proset.chains_are_sorted_length_n sorted_wrt_map)
  apply (clarsimp simp: mapf_def sorted_wrt_map)
  apply (intro conjI)
  thm sorted_wrt_mono_rel
  apply (erule sorted_wrt_mono_rel[rotated])
  apply (clarsimp simp: prosets_in_hom_iff in_hom_iff mapf_def nerve_obj_def proset.chains_are_sorted_length_n sorted_wrt_map)
  apply (erule monotone_onD)
    apply (clarsimp simp: carrier_def image_iff, metis fst_conv )
  apply (clarsimp simp: carrier_def image_iff, metis  snd_conv)
   apply (blast)
  apply (clarsimp)
  apply (clarsimp simp: prosets_in_hom_iff in_hom_iff)
  by (smt (verit) apply_iff image_iff in_mono mem_Sigma_iff prod.collapse)

term chaos_fun'

term chaos_obj

thm in_hom_simp[no_vars] 

lemma in_hom_simp': "ps.in_hom (a, b) x y \<longleftrightarrow> (ps.in_hom (x, b) x y \<and> a = x)" 

  by (safe; clarsimp simp: prosets_in_hom_iff)

lemma remdups_tl: "remdups_adj (a # xs) = remdups_adj (a # remdups_adj xs)"
  by (metis (no_types, lifting) distinct_adj_altdef distinct_adj_remdups_adj remdups_adj_Cons)

lemma map_id_chaos_obj: "x \<in> chaos_obj a \<Longrightarrow> set x \<subseteq> carrier a \<Longrightarrow> x = remdups_adj (map (($) (Id_on (carrier a))) x)" 
  apply (induct x; clarsimp)
  apply (drule meta_mp)
   apply (clarsimp simp: chaos_obj_def nondegen_def)
   apply (intro conjI)
    apply (clarsimp simp: nerve_obj_def)
  
    apply (metis chains_of.simps list.sel(3) list.simps(3))
    apply (clarsimp simp: nerve_obj_def)
  using distinct_adj_ConsD apply force
  apply (subst apply_iff)
    apply (clarsimp simp: single_valued_def)
   apply (clarsimp simp: Id_on_def, rule refl)
  apply (subst remdups_tl, clarsimp)
   apply (clarsimp simp: chaos_obj_def nondegen_def)
  by (simp add: distinct_adj_altdef)
  

lemma chains_of_carrier: "chains_of a x \<Longrightarrow> xa \<in> set x \<Longrightarrow>  xa \<in> carrier a"
  apply (induction rule: chains_of.inducts)
    apply (clarsimp, elim disjE; clarsimp)
    apply (metis Id_on_iff Un_iff carrier_def delta_hom.id_on_fst)
   apply (clarsimp)
  apply (clarsimp)
  done


sublocale traces: func "prosets.Homset" "set.Homset" "prosets.arrow" "set.arrow" chaos_obj "chaos_fun'"
  apply (standard; (clarsimp simp: in_hom_iff Hom_Syntax.arrows_iff Hom_Syntax.compatible_iff opens_dual_order.trans_rel_def)?) 
    apply (clarsimp simp: chaos_fun'_def)
    apply (intro conjI) 
  apply (clarsimp simp: prosets_in_hom_iff)
    apply (clarsimp simp: chaos_fun_def mapf_def)
  apply (subst redumps_adj_in_chaos_iff)
     apply (simp add: prosets_in_hom_iff)
    apply (intro conjI)
     apply (clarsimp)
     apply (clarsimp simp: prosets_in_hom_iff)
     apply (meson in_mono monotone_onD proset_carrier_iff)
    apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def)
    apply (subst (asm) proset.chains_are_sorted_length_n, clarsimp simp: prosets_in_hom_iff )
    apply (clarsimp simp: sorted_wrt_map)
    apply (erule sorted_wrt_mono_rel[rotated])
  apply (clarsimp simp: prosets_in_hom_iff)
  apply (smt (verit, del_insts) in_mono monotone_onD prosets_in_hom_iff)
   apply (clarsimp simp: chaos_fun'_def, intro set_eqI iffI; clarsimp simp: relcomp.simps    )
    apply (subst (asm) chaos_relcomp_distrib)
        apply (drule ps_in_hom_set_hom, simp only: snd_conv)
       apply (drule ps_in_hom_set_hom)
       apply (simp only: snd_conv)
       apply (drule ps_in_hom_set_hom)
       apply (simp only: snd_conv)



      apply (clarsimp simp:  prosets_in_hom_iff in_hom_iff)
        apply (clarsimp simp:  prosets_in_hom_iff in_hom_iff)
    apply (clarsimp simp: relcomp.simps)
  apply (subst (asm) in_hom_simp')
  find_theorems ps.in_hom
    apply (frule in_hom_simp, clarsimp)
    apply (rule_tac x=bd in exI, clarsimp)
    apply (clarsimp simp: chaos_fun_def)
    apply (rule chains_of_remdups_chaos)
    apply (frule_tac y=y in monotone_map_betw_chains)
  apply (simp only: snd_conv)
     apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def)
     apply (subst (asm) proset.chains_are_sorted_length_n) 
     apply (clarsimp simp:  prosets_in_hom_iff in_hom_iff)
  apply (clarsimp)
     apply (clarsimp simp: nerve_obj_def)
 (*    apply (erule chains_of_length[rotated])
     apply (clarsimp simp:  prosets_in_hom_iff in_hom_iff) *)
apply (subst  chaos_relcomp_distrib)
       apply (drule ps_in_hom_set_hom, simp only: snd_conv)
        apply (drule ps_in_hom_set_hom, simp only: snd_conv)
        apply (drule ps_in_hom_set_hom, simp only: snd_conv)


      apply (clarsimp simp:  prosets_in_hom_iff in_hom_iff)
        apply (clarsimp simp:  prosets_in_hom_iff in_hom_iff)
    apply (clarsimp simp: relcomp.simps)
   apply (blast)
  apply (clarsimp simp:  prosets_identity prosets_in_hom_iff opens_order.set_identity) 
  apply (safe) 
   apply (clarsimp simp: chaos_fun'_def)
   apply (rule Id_on_eqI[rotated], assumption) 
  apply (clarsimp simp: chaos_fun_def mapf_def)
   apply (erule (1) map_id_chaos_obj)
  apply (clarsimp simp: chaos_fun'_def chaos_fun_def relcomp.simps mapf_def)
  apply (intro conjI)
  apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def)

   apply (meson chains_of_carrier)
  apply (rule map_id_chaos_obj, assumption)
apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def)

  apply (meson chains_of_carrier)
  done



sublocale chaos_pre: func_comp "dual_opens_order_category.op.Homset"   "prosets.Homset" "set.Homset" dual_opens_order_category.op.arrow  "prosets.arrow" "set.arrow" \<Omega> "\<lambda>(x,y). (\<Omega> y, rest (x, y)) " chaos_obj chaos_fun' .. 

sublocale chaos: presheaf "opens_order.category_of.arrow" "opens_order.category_of.Homset" "chaos_obj o \<Omega>" "chaos_fun' o (\<lambda>(x,y). (\<Omega> y, rest (x, y)) )" ..


end


locale tuple_system =
  fixes \<DD> :: "'a set set" and T :: "'b set" and d :: "'b \<Rightarrow> 'a set" and down :: "('b \<times> 'a set) \<Rightarrow> 'b" 
  assumes a1: "U \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> U \<subseteq> d x \<Longrightarrow> d (down (x, U)) = U" and
          a2: "U \<in> \<DD> \<Longrightarrow> W \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> U \<subseteq> W  \<Longrightarrow> W \<subseteq> d x \<Longrightarrow> down ((down (x, W)), U) = down (x, U)" and
          a3: "U \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> d x = U \<Longrightarrow> (down (x, U)) = x" and
          a4: "U \<in> \<DD> \<Longrightarrow> W \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> y \<in> T \<Longrightarrow> d x = U \<Longrightarrow> d y = W \<Longrightarrow>   down (x, (U \<inter> W)) = down (y, (U \<inter> W)) \<Longrightarrow> \<exists>z\<in>T.  d z = (U \<union> W) \<and> down (z, U) = x \<and> down (z, W) = y" and
          a5: "U \<in> \<DD> \<Longrightarrow> x \<in> T \<Longrightarrow> d x = U \<Longrightarrow> W \<in> \<DD> \<Longrightarrow>  U \<subseteq> W  \<Longrightarrow> \<exists>y\<in>T. d y = W \<and>  (down (y, U)) = x"

context Omega

begin

definition "chaos U = (U, chaos_pre.functor_of.fobj U)" 

definition "d = fst"

primrec down where "down (x, v) = (v, chaos_pre.functor_of.farr (v, fst x) `` snd x)"



lemma finite_union_open: "x \<in> open \<Longrightarrow> y \<in> open \<Longrightarrow> x \<union> y \<in> open"
  by (insert open_Union, atomize, erule_tac x="{x,y}" in allE, clarsimp)


find_consts name: monotone



lemma chains_of_monotone:" chains_of R xs \<Longrightarrow> proset R \<Longrightarrow> monotone_on (set xs) (\<lambda>x y. (x, y) \<in> R)  (\<lambda>x y. (x, y) \<in> R') f \<Longrightarrow> chains_of R'  (map f xs)"
  thm chains_of.induct
  apply (induct rule: chains_of.induct; clarsimp?)
  
   apply (rule cons_step)
    apply (atomize)
    apply (drule mp)
     apply (rule monotone_onI)
  using monotone_onD 
     apply fastforce
    apply (assumption)    apply (meson insertCI monotone_onD)
  apply (rule single)
  apply (clarsimp simp: proset.carrier_refl)
  apply (clarsimp simp: carrier_def image_iff) 

  using monotone_onD by fastforce

lemma chains_of_in_carrier: "chains_of R xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> carrier R"
  apply (induction rule:chains_of.inducts; clarsimp)
  apply (erule chains_of.cases; clarsimp?)
   apply (elim disjE; clarsimp)
  apply (clarsimp simp: carrier_def image_iff)
   apply (metis fst_conv)
  apply (elim disjE; clarsimp)
apply (clarsimp simp: carrier_def image_iff)
  apply (metis fst_conv)
  done

term chaos_fun'

lemma chaos_fun_rest_Image:  assumes S_is_chaos: "S = chaos_obj (\<Omega> b)" and rest_defined:" a \<subseteq> b" shows "a \<in> open \<Longrightarrow> b \<in> open \<Longrightarrow> chaos_fun' (\<Omega> b,  rest (a, b)) `` S = (remdups_adj o map (\<lambda>x. constrain x a)) ` S"
  apply (safe; clarsimp simp: image_iff chaos_fun'_def )
   apply (clarsimp simp: chaos_fun_def mapf_def rest_def)
   apply (rule_tac x=xb in bexI)
    apply (rule arg_cong[where f=remdups_adj])
    apply (rule list.map_cong0)
  apply (subst apply_iff, clarsimp simp: single_valued_def)
     apply (clarsimp)
     apply (intro conjI)
      apply (drule_tac c=z in subsetD; clarsimp)
     apply (rule refl)
  apply (rule refl)
   apply (clarsimp)
  apply (rule_tac x=xa in bexI)
   apply (subst (asm) S_is_chaos)
   apply (clarsimp)
  apply (clarsimp simp: chaos_fun_def relcomp.simps)
    apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def)

    apply (clarsimp simp: chaos_fun_def relcomp.simps mapf_iff)
    apply (intro conjI)
    apply (clarsimp simp: rest_def image_iff chaos_obj_def nondegen_def nerve_obj_def)
    apply (erule (1) chains_of_in_carrier)
   apply (rule arg_cong[where f=remdups_adj])
   apply (rule list.map_cong0)
   apply (safe)
   apply (subst apply_iff)
     apply (clarsimp simp: single_valued_def rest_def)
    apply (clarsimp simp: rest_def)   
    apply (intro conjI)
     defer
     apply (rule refl, clarsimp)
   apply (subst (asm) apply_iff)
     apply (clarsimp simp: single_valued_def rest_def)
    apply (clarsimp simp: rest_def)   
    apply (intro conjI)
     defer
     apply (rule refl)
    apply (clarsimp)
 

   apply (erule (1) chains_of_in_carrier)

    apply (clarsimp simp: rest_def image_iff chaos_obj_def nondegen_def nerve_obj_def)
  apply (erule (1) chains_of_in_carrier)
  done

lemma sorted_wrt_remdups_adj[simp]:
  "sorted_wrt r xs \<Longrightarrow> sorted_wrt r (remdups_adj xs)" 
  apply (induct xs; clarsimp)
  by (smt (verit) list.sel(1) list.sel(3) remdups_adj.elims remdups_adj_set sorted_wrt.elims(1))

lemma rest_union: "(x, y) \<in> \<Omega> (a \<union> aa) \<Longrightarrow> (restrict x (- a), restrict y (- a)) \<in> \<Omega> a"
  apply (clarsimp simp: om_iff)
  apply (intro conjI)
    apply (simp add: single_valued_restrictI)
  apply (simp add: single_valued_restrictI)
  apply (clarsimp)
  by (metis Compl_iff fst_eqD restrict_iff snd_eqD)

lemma rest_subset: "(x, y) \<in> \<Omega> (w) \<Longrightarrow> u \<subseteq> w \<Longrightarrow> (restrict x (- u), restrict y (- u)) \<in> \<Omega> u"
  apply (clarsimp simp: om_iff)
  apply (intro conjI)
    apply (simp add: single_valued_restrictI)
  apply (simp add: single_valued_restrictI)
  apply (clarsimp)
  by (metis Compl_iff fst_eqD restrict_iff snd_eqD)

lemma un_cancellative: "X \<union> Y = X \<union> Z \<Longrightarrow> Y \<inter> X = {} \<Longrightarrow> Z \<inter> X = {} \<Longrightarrow> Y = Z" 
  apply (safe; clarsimp?)
   apply blast
  apply blast
  done

lemma dom_in_om:"(a, b) \<in> \<Omega> (W) \<Longrightarrow> fst ` a \<subseteq> W \<and> fst ` b \<subseteq> W"
  apply (clarsimp simp: om_iff)
  by (metis fst_conv image_iff)

lemma dom_not_in_minus_om:"(a, b) \<in> \<Omega> (W - x) \<Longrightarrow> (a', b') \<in> \<Omega> (x) \<Longrightarrow> a \<inter> a' = {}"
  apply (drule dom_in_om)+
  apply (clarsimp simp: om_iff)
  apply (safe; clarsimp)
  by blast

lemma dom_not_in_minus_om':"(a, b) \<in> \<Omega> (W - x) \<Longrightarrow> (a', b') \<in> \<Omega> (x) \<Longrightarrow> b \<inter> b' = {}"
  apply (drule dom_in_om)+
  apply (clarsimp simp: om_iff)
  apply (safe; clarsimp)
  by blast


lemma subset_carrierI: "proset R \<Longrightarrow> (\<And>x. x \<in> xs \<Longrightarrow> (x, x) \<in> R) \<Longrightarrow> xs \<subseteq> carrier R"
  by (meson proset_carrier_iff subsetI)

lemma subset_carrier_iff: "proset R \<Longrightarrow> xs \<subseteq> carrier R \<longleftrightarrow> (\<forall>x\<in>xs. (x, x) \<in> R) "
  by (meson in_mono proset_carrier_iff subset_carrierI)


lemma restrict_is_trace: "x \<in> open \<Longrightarrow> W \<in> open \<Longrightarrow> x \<subseteq> W \<Longrightarrow>  set xa \<subseteq> carrier (\<Omega> x) \<Longrightarrow> \<Omega> W \<noteq> {} \<Longrightarrow> (a, b) \<in> \<Omega> W \<Longrightarrow> (xb, xb') \<in> \<Omega> x \<Longrightarrow>
       xb \<in> set xa \<Longrightarrow> xb' \<in> set xa \<Longrightarrow> (restrict a x \<union> xb, restrict a x \<union> xb') \<in> \<Omega> W"
  apply (clarsimp simp: om_iff subset_carrier_iff is_proset)
  apply (frule_tac x=xb in bspec; clarsimp)
  apply (intro conjI; clarsimp?)
     apply (smt (z3) Un_iff fst_conv restrict_iff single_valued_def)
  defer
  defer
  apply (elim disjE; clarsimp?)
   apply (metis Omega.in_open_in_univ Omega.omega_to_preord Omega.proset_carrier_iff
              Omega_axioms fst_conv proset.refl_rel refl_on_domain restrict_iff snd_conv)
    apply (smt (verit, best) fst_eqD in_mono snd_conv)
     apply (smt (z3) Un_iff fst_conv restrict_iff single_valued_def)
  by (metis image_Un)

lemma refl_on_carrier: "x \<in> open \<Longrightarrow> v \<in> carrier (\<Omega> x) \<Longrightarrow> (v, v) \<in> \<Omega> x"
  by (simp add: is_proset proset_carrier_iff)

lemma restrict_carrier_omega: "W \<in> open \<Longrightarrow> x \<subseteq> W \<Longrightarrow> x \<in> open \<Longrightarrow> s \<in> carrier (\<Omega> W) \<Longrightarrow>  restrict s (-x) \<in> carrier (\<Omega> x)" 
  apply (clarsimp simp: carrier_om_iff)
  apply (intro conjI)
   apply (simp add: single_valued_restrictI)
  by (clarsimp simp: Ball_def restrict_iff)

lemma empty_carrier_iff[simp]: "set xs \<subseteq> carrier {} \<longleftrightarrow> xs = []"
  by (clarsimp simp: carrier_def)

lemma constrain_to_subset: "W \<in> open \<Longrightarrow> x \<subseteq> W \<Longrightarrow> x \<in> open \<Longrightarrow> (remdups_adj \<circ> map (\<lambda>xa. restrict xa (- x))) ` chaos_obj (\<Omega> W) = chaos_obj (\<Omega> x)"
  apply (safe; clarsimp) [1]
      apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def)
   apply (clarsimp simp: proset.chains_are_sorted_length_n is_proset)
  apply (intro conjI)
 apply (rule sorted_wrt_remdups_adj, clarsimp simp: sorted_wrt_map)
      apply (erule sorted_wrt_mono_rel[rotated])
    apply (erule (1) rest_subset)
  apply (clarsimp simp: image_iff)
  apply (erule (2) restrict_carrier_omega)
   apply (drule_tac c=xaa in subsetD; clarsimp?)
  apply (clarsimp simp: image_iff)
  apply (clarsimp simp: chaos_obj_def nondegen_def nerve_obj_def  proset.chains_are_sorted_length_n is_proset)

  apply (case_tac "\<Omega> (W) = {}"; clarsimp?)
  
  apply (smt (verit) Omega.carrier_om_iff Omega_axioms empty_carrier_iff subset_iff)

    apply (subgoal_tac "\<exists>s. s \<in> \<Omega> (W)"; clarsimp simp: image_iff Bex_def)
    apply (rule_tac x="map (\<lambda>v. union (restrict a (x)) v) xa" in exI)
    apply (intro conjI)

 apply (clarsimp simp: sorted_wrt_map)
        apply (erule sorted_wrt_mono_rel[rotated])
  apply (erule (8) restrict_is_trace)
        
        apply ( rule subset_carrierI, clarsimp simp: is_proset)
       apply (clarsimp)
       apply (rule  restrict_is_trace; assumption?)
  apply (erule refl_on_carrier)
  apply blast

      apply (subst distinct_adj_map_iff)
        apply (rule inj_onI)
        apply (drule un_cancellative)
          prefer 5
          apply (clarsimp)
          apply (subst map_idI)
           apply (clarsimp simp: restrict_def)
           apply (safe; clarsimp)
 
          apply (smt (verit) Omega.carrier_om_iff Omega_axioms fst_conv image_subset_iff in_mono)
         apply (simp add: distinct_adj_altdef)
  apply (safe; clarsimp?)
  
        apply (metis Id_on_iff Omega.carrier_om_iff Omega_axioms delta_hom.id_on_fst in_mono restrict_iff)
       apply (safe; clarsimp?)
        apply (metis Id_on_iff Omega.carrier_om_iff Omega_axioms delta_hom.id_on_fst in_mono restrict_iff)
      apply (clarsimp)
   apply (clarsimp)
  by (fastforce)

lemma dual_order_hom_iff: "dual_opens_order_category.opHom.in_hom f a b \<longleftrightarrow> (a \<in> open \<and> b \<in> open \<and> b \<subseteq> a \<and> f = (b, a))"
  apply (clarsimp simp:  opens_dual_order.arr_iff opens_order.arr_iff opens_order.proset_hom_def)
  by (safe)

(* Proof that chaos forms a tuple system *)
sublocale tuple_system "open" "chaos ` open" d down
  apply (standard)
      apply (clarsimp simp: down_def d_def)
     apply (clarsimp simp: down_def d_def chaos_def)
     apply (subst relcomp_Image[symmetric])
  thm chaos_pre.functor_of.hom[simplified comp_def opens_dual_order.trans_rel_def, symmetric, simplified case_prod_beta, where f="(_, _)" and g = "(_, _)", simplified ]
  using chaos_pre.functor_of.hom[simplified comp_def opens_dual_order.trans_rel_def, symmetric, simplified opens_order.arr_iff] 
     apply (subst chaos_pre.functor_of.hom[simplified comp_def opens_dual_order.trans_rel_def, symmetric, simplified case_prod_beta, where f="(_, _)" and g = "(_, _)", simplified ], clarsimp simp: opens_order.arr_iff)
       apply (intro conjI refl)
        apply (rule refl)
       apply (rule refl)
      apply (clarsimp simp:  opens_order.arr_iff, rule refl)
     apply (clarsimp)
    apply (clarsimp simp: down_def chaos_def d_def)
    defer
  apply (clarsimp simp: image_iff)
    apply (clarsimp simp: chaos_def d_def)
    apply (intro conjI)
      apply (simp add: finite_union_open)
     apply (subst chaos_fun_rest_Image; clarsimp simp: finite_union_open)
     apply (rule constrain_to_subset[simplified comp_def]; clarsimp simp: finite_union_open)
     apply (subst chaos_fun_rest_Image; clarsimp simp: finite_union_open)
    apply (rule constrain_to_subset[simplified comp_def]; clarsimp simp: finite_union_open )

    apply (clarsimp)
    apply (clarsimp simp: d_def chaos_def)
     apply (subst chaos_fun_rest_Image; clarsimp)

   apply (rule constrain_to_subset[simplified comp_def]; clarsimp)
    apply (subst chaos_fun_rest_Image; clarsimp)

  apply (rule constrain_to_subset[simplified comp_def]; clarsimp simp: finite_union_open )
  done

end




end
