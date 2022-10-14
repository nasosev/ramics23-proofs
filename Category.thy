theory Category
imports Orders
begin

locale Hom_Syntax = 
  fixes Hom :: "('obj \<times> 'arrow \<times> 'obj) set" and arr ::
  "'arrow \<Rightarrow> 'arrow \<Rightarrow> 'arrow"

begin

abbreviation in_hom   
  where "in_hom f a b \<equiv> (a, f, b) \<in> Hom"

notation in_hom ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

abbreviation sources   
  where "sources f a \<equiv> \<exists>b. (a, f, b) \<in> Hom"

notation sources ("\<guillemotleft>_ : _ \<rightarrow> ?\<guillemotright>")

abbreviation targets   
  where "targets f a \<equiv> \<exists>b. (b, f, a) \<in> Hom"

notation targets ("\<guillemotleft>_ : ? \<rightarrow> _\<guillemotright>")

definition "hom_of a b = {f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>}"  

definition "arrows \<equiv> (\<lambda>c. fst (snd c)) ` Hom"

lemma arrows_iff:  "f \<in> arrows \<longleftrightarrow> (\<exists>a b. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>)"
  by (clarsimp simp: arrows_def image_iff Bex_def)

definition "arrcompose \<equiv> (\<lambda>f g. (fst f, arr ((fst o snd) f) ((fst o snd) g), (snd o snd) g))"

declare arrcompose_def[simp]

definition "compatiblity = {(f, g). f \<in> Hom \<and> g \<in> Hom \<and> snd (snd f) = (fst g)}"

abbreviation compatible   
  where "compatible f g \<equiv> (f, g) \<in> compatiblity"

notation compatible (infixr "#>"  50)

lemma compatible_iff: "x #> y \<longleftrightarrow> (x \<in> Hom \<and> y \<in> Hom \<and> snd (snd x) = fst y)"
  by (clarsimp simp: compatiblity_def)


end

locale pre_category = Hom_Syntax Hom arr + a: unital_magma arr arrows + 
   partial_semigroup compatiblity arrcompose  
   for arr :: "'arrow \<Rightarrow> 'arrow \<Rightarrow> 'arrow" and Hom :: "('obj \<times> 'arrow \<times> 'obj) set"  +
   assumes id_exists: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<Longrightarrow> \<exists>i i'. \<guillemotleft>i' : a \<rightarrow> a\<guillemotright> \<and> \<guillemotleft>i : b \<rightarrow> b\<guillemotright>"

begin

lemma in_units_iff: "(a, f, b) \<in> Hom \<Longrightarrow> f \<in> a.idems \<longleftrightarrow>  (arr f f = f)"
  apply (intro iffI)
   apply (clarsimp simp: a.idems_def )
  apply (clarsimp simp: a.idems_def image_iff arrows_iff)
  apply (metis)
  done

end

locale category = pre_category arr Hom 
     for arr :: "'arrow \<Rightarrow> 'arrow \<Rightarrow> 'arrow" and Hom :: "('obj \<times> 'arrow \<times> 'obj) set" +
  assumes uniq_id: "(a, f, a) \<in> Hom \<Longrightarrow> \<exists>!i \<in> a.idems.  (a, i, a) \<in> Hom \<and> (\<forall>g. (\<guillemotleft>g : a \<rightarrow> ?\<guillemotright> \<longrightarrow> arr i g = g) \<and> (\<guillemotleft>g : ? \<rightarrow> a\<guillemotright> \<longrightarrow> arr g i = g))"


begin

definition "identity (a :: 'obj) \<equiv> (THE f. (a, f, a) \<in> Hom \<and>  f \<in> a.idems \<and> (\<forall>g. (\<guillemotleft>g : a \<rightarrow> ?\<guillemotright> \<longrightarrow> arr f g = g) \<and> (\<guillemotleft>g : ? \<rightarrow> a\<guillemotright> \<longrightarrow> arr g f = g) ))"

lemma  carrier_simp[simp]: "x \<in> carrier compatiblity \<longleftrightarrow> x \<in> Hom"
  apply (clarsimp simp: carrier_def Ball_def Hom_Syntax.compatible_iff image_iff, safe; clarsimp)
   using compatible_iff apply blast
   using compatible_iff apply blast 
   by (metis compatible_iff eq_snd_iff fst_conv id_exists)

lemma  carrier_simp'[simp]: "(a, f, b) \<in> carrier {(f, g). f \<in> Hom \<and> g \<in> Hom \<and> (snd o snd) f = (snd o snd) g} \<longleftrightarrow> (a, f, b) \<in> Hom"
  by (clarsimp simp: carrier_def image_iff, safe; clarsimp)

lemma id_in_hom_l[simp]: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<Longrightarrow> \<guillemotleft>identity a : a \<rightarrow> a\<guillemotright>" 
  apply (clarsimp simp: identity_def) 
  apply (rule the1I2)
  apply (frule id_exists, clarsimp)
   apply (frule uniq_id)
   apply (elim ex1E, clarsimp)
   apply (metis)
  apply (clarsimp)
  done

lemma id_comp_l[simp]: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<Longrightarrow> arr (identity a) f = f" 
  apply (clarsimp simp: identity_def) 
  apply (rule the1I2)
  apply (frule id_exists, clarsimp)
   apply (frule uniq_id)
   apply (elim ex1E, clarsimp)
   apply (metis)
  apply (blast)
  done

lemma id_in_hom_r[simp]: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<Longrightarrow> \<guillemotleft>identity b : b \<rightarrow> b\<guillemotright>" 
  apply (clarsimp simp: identity_def) 
  apply (rule the1I2)
  apply (frule id_exists, clarsimp)
   apply (frule uniq_id) back
   apply (elim ex1E, clarsimp)
  apply metis
   apply (blast)
  done

lemma id_comp_r[simp]: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<Longrightarrow> arr f (identity b) = f" 
  apply (clarsimp simp: identity_def) 
  apply (rule the1I2)
  apply (frule id_exists, clarsimp)
   apply (frule uniq_id) back
   apply (elim ex1E, clarsimp)
   apply (metis)
  apply (blast)
  done
  

sublocale partial_monoid compatiblity arrcompose "\<Union>(a,f,b)\<in>Hom. {(a, identity a, a), (b, identity b, b)}"  
  apply (unfold_locales; clarsimp)
    apply (rule_tac x="(a, aa, b)" in bexI)
     apply (rule_tac x="(a, identity a, a)" in bexI; clarsimp simp: rev_image_eqI compatible_iff)
    apply (assumption)
   apply (rule_tac x="(a, aa, b)" in bexI)
     apply (rule_tac x="(b, identity b, b)" in bexI; clarsimp simp: rev_image_eqI compatible_iff)
   apply (assumption)
  apply (elim disjE; clarsimp simp: compatible_iff)
  done


abbreviation (input) "Homset \<equiv> Hom"

abbreviation (input) "arrow \<equiv> arr"

lemma hom_comp: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<Longrightarrow> \<guillemotleft>g : b \<rightarrow> c\<guillemotright> \<Longrightarrow> \<guillemotleft>arr f g : a \<rightarrow> c\<guillemotright>" 
  apply (insert D_assoc[simplified], clarsimp simp: compatible_iff)
  by (smt (verit, best) id_comp_l id_in_hom_l)

lemma arr_assoc: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<Longrightarrow> \<guillemotleft>g : b \<rightarrow> c\<guillemotright> \<Longrightarrow> \<guillemotleft>h : c \<rightarrow> d\<guillemotright> \<Longrightarrow> arr (arr f g) h = arr f (arr g h) " 
  apply (insert D_assoc[simplified], insert times_assoc[simplified], clarsimp simp: compatible_iff)
  by (smt (verit, best) id_comp_l id_in_hom_l)

end

lemma fst_converse_snd[simp]: "fst ` converse R = snd ` R"
  by (safe; fastforce simp: image_iff Bex_def)

lemma snd_converse_fst[simp]: "snd ` converse R = fst ` R"
  by (safe; fastforce simp: image_iff Bex_def)

lemma carrier_converse_is_carrier: "carrier (Hom\<inverse>) = carrier Hom"
  by (safe; clarsimp simp: carrier_def)


locale op_category = category 

begin

abbreviation "opHom \<equiv> {(a, f, b). (b, f, a) \<in> Hom}"

lemma arrows_simp: "image (\<lambda>c. fst (snd c)) opHom  = image (\<lambda>c. fst (snd c)) Hom"
  apply (safe; clarsimp simp: image_iff)
   apply (metis fst_conv snd_conv)
  by (metis)


end

sublocale  op_category \<subseteq> opHom: Hom_Syntax opHom "(\<lambda>a b. arr b a)" done


sublocale op_category \<subseteq> unital_magma "(\<lambda>a b. arr b a)" "opHom.arrows"
  apply (unfold_locales; (clarsimp simp: arrows_simp)?)
   apply (smt (z3) Collect_cong arrows_def arrows_iff arrows_simp id_comp_r id_in_hom_r in_units_iff magma.idems_def opHom.arrows_def)
  by (smt (z3) Collect_cong arrows_def arrows_iff arrows_simp id_comp_l id_in_hom_l in_units_iff magma.idems_def opHom.arrows_def)



sublocale op_category \<subseteq> op: category "(\<lambda>a b. arr b a)" "opHom" 
  apply (unfold_locales; clarsimp simp: opHom.compatible_iff carrier_converse_is_carrier )
     apply (safe)
        apply (clarsimp)
  using hom_comp apply presburger
  using hom_comp apply presburger
  using arr_assoc apply force
  using id_in_hom_r apply blast
  using id_in_hom_l apply blast
  defer
   apply metis
  apply (rule_tac x="identity a" in exI, clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: idems_def opHom.arrows_iff)
   apply (intro conjI)
    apply (rule_tac x=a in exI)
  apply (rule_tac x=a in exI)
    apply simp
  using id_comp_r id_in_hom_r apply blast
  apply (clarsimp)
  by fastforce



locale func = source: category arr Hom + target: category arr' Hom'
  for Hom :: "('obj \<times> 'arr \<times> 'obj) set" and Hom' :: "('obj' \<times> 'arr' \<times> 'obj') set" 
  and arr  and arr' +
   fixes F_obj :: "'obj \<Rightarrow> 'obj'" and F_arr :: "'arr \<Rightarrow> 'arr'"
   assumes source_target: "(a, f, b) \<in> Hom \<Longrightarrow> (F_obj a, F_arr f, F_obj b) \<in> Hom'"
   assumes hom: "(a, f, b) \<in> Hom \<Longrightarrow> (b, g, c) \<in> Hom \<Longrightarrow>  F_arr (arr f g) = arr' (F_arr f) (F_arr g)"
   assumes func_id: "(a, f, a) \<in> Hom \<Longrightarrow> F_arr (source.identity a) = target.identity (F_obj a) "

begin

abbreviation (input) "fobj \<equiv> F_obj"
abbreviation (input) "farr \<equiv> F_arr"


end


locale subcategory_pre = category + 
  fixes objects :: "'b set" and arrows :: "'a set"
begin

definition "subhom = {(a, f, b). a \<in> objects \<and> b \<in> objects \<and> f \<in> arrows \<and> \<guillemotleft> f : a \<rightarrow> b\<guillemotright>} "

sublocale sc: Hom_Syntax  subhom arr done

lemma in_hom_iff: "sc.in_hom f a b \<longleftrightarrow> a \<in> objects \<and> b \<in> objects \<and> f \<in> arrows \<and> \<guillemotleft> f : a \<rightarrow> b\<guillemotright>"
  by (clarsimp simp: subhom_def)


end


locale subcategory = subcategory_pre +
  assumes (*subhom: "\<guillemotleft> f : a \<rightarrow> b\<guillemotright> \<Longrightarrow> \<exists>a' f' b'. a' \<in> objects \<and> b' \<in> objects \<and> f' \<in> arrows \<and> \<guillemotleft> f' : a' \<rightarrow> b'\<guillemotright>" and *)
          arrow_closed: "f \<in> sc.arrows \<Longrightarrow> g \<in> sc.arrows \<Longrightarrow> arr f g \<in> arrows" and
          id_closed: "a \<in> objects \<Longrightarrow> identity a \<in> arrows"

begin


lemma in_sc_arrows_in: "a \<in> sc.arrows \<Longrightarrow> a \<in> arrows"
  by (clarsimp simp: sc.arrows_iff subhom_def Hom_Syntax.arrows_def)

sublocale subcat: category arr subhom
  apply (standard; (clarsimp simp: Hom_Syntax.arrows_def Hom_Syntax.compatiblity_def sc.arrows_iff subhom_def sc.compatible_iff)?)
       apply (clarsimp simp: magma.idems_def)
       apply (rule_tac x=a in exI; clarsimp)
       apply (rule_tac x="identity a" in exI; clarsimp)
       apply (rule_tac x=a in exI; clarsimp)
  apply (frule id_closed, simp only: sc.arrows_iff, clarsimp simp: subhom_def)
  using id_closed id_comp_r id_in_hom_l apply blast
       apply (clarsimp simp: magma.idems_def)

 apply (rule_tac x=b in exI; clarsimp)
       apply (rule_tac x="identity b" in exI; clarsimp)
  apply (rule_tac x=b in exI; clarsimp)
  using sc.arrows_iff subhom_def id_closed id_comp_l id_in_hom_r apply blast
     apply (safe; clarsimp)
        apply (rule in_sc_arrows_in, clarsimp simp: sc.arrows_iff in_hom_iff)
  apply (metis Hom_Syntax.arrows_iff arrow_closed hom_comp local.in_hom_iff)
  using hom_comp apply blast
  apply (rule in_sc_arrows_in, clarsimp simp: sc.arrows_iff in_hom_iff)
  apply (metis Hom_Syntax.arrows_iff arrow_closed hom_comp local.in_hom_iff)
  using hom_comp apply presburger
    apply (simp add: arr_assoc)
   apply (rule_tac x="identity b" in exI)
   apply (rule_tac x="identity a" in exI)
  apply (simp add: id_closed in_sc_arrows_in)
  apply (rule_tac a="identity a" in ex1I; clarsimp simp: image_iff magma.idems_def id_closed )
   apply (intro conjI allI impI)
  using id_in_hom_l apply blast
  using id_closed id_comp_l id_in_hom_r apply blast
  using id_closed id_comp_l id_in_hom_r apply blast
  using id_closed id_comp_r id_in_hom_r apply blast
  by (metis id_closed id_comp_l id_in_hom_r)
end

locale func_comp = source: func Hom_A Hom_B arr_A arr_B f_obj f_arr + target:  func Hom_B Hom_C arr_B arr_C f_obj' f_arr'
  for Hom_A Hom_B Hom_C arr_A arr_B arr_C f_obj f_arr  f_obj' f_arr'
begin

sublocale functor_of: func Hom_A Hom_C arr_A arr_C "f_obj' o f_obj" "f_arr' o f_arr"
  apply (standard)
    apply (simp add: source.source_target target.source_target)
   apply (smt (verit) comp_eq_dest_lhs func.axioms(3) func_axioms_def source.func_axioms target.func_axioms)
  by (metis comp_apply source.func_id source.source_target target.func_id)

end

locale contravariant_func = op_source: op_category arr_A Hom_A   + func "op_source.op.Homset" Hom_B "op_source.op.arrow" arr_B F_obj F_arrow
  for Hom_A arr_A Hom_B arr_B F_obj F_arrow

end