theory Partial_Semigroups
imports Main
begin

definition "carrier R = fst ` R \<union> snd ` R"


locale partial_semigroup =
  fixes D :: "('a \<times> 'a) set" and times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<Zspot>" 70)
  assumes D_assoc: "(y, z) \<in> D  \<and> (x, (y \<Zspot> z)) \<in> D  \<longleftrightarrow> (x, y) \<in> D \<and> (x \<Zspot> y, z) \<in> D "
  assumes times_assoc: "(x, y) \<in> D \<Longrightarrow> (x \<Zspot> y, z) \<in> D \<Longrightarrow> (x \<Zspot> (y \<Zspot> z)) = ((x \<Zspot> y) \<Zspot> z)"
begin

lemma D_assoc': "(y, z) \<in> D \<Longrightarrow>  (x, (y \<Zspot> z)) \<in> D  \<Longrightarrow> (x, y) \<in> D "
  by (meson partial_semigroup.D_assoc partial_semigroup_axioms)

lemma ptimes_assocD_var1: "(y, z) \<in> D  \<Longrightarrow> (x, times y z) \<in> D \<Longrightarrow> (x, y) \<in> D \<and> ((times x y), z) \<in>  D "
  using D_assoc by blast

lemma ptimes_assocD_var2: "(x, y) \<in> D \<Longrightarrow> ((times x y), z) \<in>  D \<Longrightarrow> (y, z) \<in> D \<and> (x, times y z) \<in> D" 
  apply (intro conjI)
  using D_assoc apply blast
  using D_assoc by blast

lemma ptimes_assoc_var: "(y, z) \<in> D \<Longrightarrow> (x, times y z) \<in> D \<Longrightarrow> (x \<Zspot> (y \<Zspot> z)) = ((x \<Zspot> y) \<Zspot> z)"
  using ptimes_assocD_var1 times_assoc by blast

end

locale partial_monoid = partial_semigroup +
  fixes E :: "'a set"
  assumes unitl_ex: "x \<in> carrier D \<Longrightarrow> \<exists>e\<in>E. ((e, x) \<in> D \<and> (e \<Zspot> x = x))"
  and unitr_ex: "x \<in> carrier D \<Longrightarrow> \<exists>e \<in> E. (x, e) \<in> D \<and> (x \<Zspot> e = x)"
  and units_eq: "e \<in> E \<Longrightarrow> e' \<in> E \<Longrightarrow> (e, e') \<in> D  \<Longrightarrow>  e = e'"

begin



abbreviation "lid x \<equiv> (THE e. e \<in> E  \<and> (e, x) \<in> D \<and> (e \<Zspot> x = x))"

abbreviation "rid x \<equiv> (THE e. e \<in> E  \<and> (x, e) \<in> D \<and> (x \<Zspot> e = x))"


lemma lid_id[simp]: "x \<in> carrier D \<Longrightarrow> lid x \<Zspot> x = x" 
  apply (rule the1I2)
   apply (insert unitl_ex[where x=x], clarsimp)
   apply (rule_tac a=e in ex1I)
    apply (clarsimp)
   apply (clarsimp)
   apply (metis partial_monoid.units_eq partial_monoid_axioms partial_semigroup.D_assoc partial_semigroup_axioms)
  apply (clarsimp)
  done

lemma lid_defined[simp]: "x \<in> carrier D \<Longrightarrow> (lid x, x) \<in> D" 
  apply (rule the1I2)
 apply (insert unitl_ex[where x=x], clarsimp)
   apply (rule_tac a=e in ex1I)
    apply (clarsimp)
   apply (clarsimp)
   apply (metis partial_monoid.units_eq partial_monoid_axioms partial_semigroup.D_assoc partial_semigroup_axioms)
  apply (clarsimp)
  done

lemma rid_id[simp]: "x \<in> carrier D \<Longrightarrow> x \<Zspot> rid x = x" 
  apply (rule the1I2)
   apply (insert unitr_ex[where x=x], clarsimp)
   apply (rule_tac a=e in ex1I)
    apply (clarsimp)
   apply (clarsimp)
  apply (rule units_eq; clarsimp?)
  apply (metis ptimes_assocD_var2)
  apply (clarsimp)
  done

lemma rid_defined[simp]: "x \<in> carrier D \<Longrightarrow>(x, rid x) \<in> D" 
  apply (rule the1I2)
 apply (insert unitr_ex[where x=x], clarsimp)
   apply (rule_tac a=e in ex1I)
    apply (clarsimp)
   apply (clarsimp)
   apply (metis partial_monoid.units_eq partial_monoid_axioms partial_semigroup.D_assoc partial_semigroup_axioms)
  apply (clarsimp)
  done
  
end


locale pas = partial_semigroup + 
 assumes D_commute: "sym D"
 assumes times_commute: "(x,y) \<in> D \<Longrightarrow> times x y = times y x"

begin

definition "unit x y \<equiv> (x, y) \<in> D \<and> (times x y = x)"


end

find_consts name:equiv

locale pis = partial_semigroup + 
 assumes D_idem: "refl_on (carrier D) D"
 assumes times_idemp: "(x,x) \<in> D \<Longrightarrow> times x x = x"


locale semigroup = partial_semigroup +
  fixes S :: "'a set"
  assumes closed: "(x \<in> S \<and> y \<in> S) \<longleftrightarrow> (x, y) \<in> D"
  assumes closed_times: "(x \<in> S \<and> y \<in> S) \<Longrightarrow> (times x y) \<in> S"
  assumes total_on: "S = (carrier D)"
begin

find_theorems name: image_iff

lemma assoc:  "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> z \<in> S \<Longrightarrow> (times x (times y z)) = (times (times x y) z)"
  using closed times_assoc 
  by (meson closed_times)

end

locale abel_semigroup = pas + semigroup
begin

lemma commute: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> (times x y) = (times y x)"
  using closed times_commute by blast

end

locale idemp_semigroup = semigroup + pis
begin

lemma idemp: "x \<in> S \<Longrightarrow> times x x = x"
  using closed times_idemp by blast

end


locale magma = fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<Zspot>" 70) and  S :: "('a) set"

begin

definition "idems = {x. x \<in> S \<and> times x x = x}"


end


locale unital_magma = magma +
  assumes unitl_ex1: " x \<in> S \<Longrightarrow> \<exists>l\<in>idems.((times :: 'a \<Rightarrow> 'a \<Rightarrow> 'a) l x = x)"
  and unitr_ex1: "x \<in> S \<Longrightarrow> \<exists>r\<in>idems. times x r = x"

begin



definition "left x \<equiv> (THE e. e \<in> S \<and> e \<Zspot> x = x)"

definition "right x \<equiv> (THE e. e \<in> S \<and> x \<Zspot> e = x)"

end

end