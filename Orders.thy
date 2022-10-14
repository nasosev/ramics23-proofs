theory Orders
imports Partial_Semigroups
begin

locale transitive  = 
  fixes R :: "('a) rel"
  assumes trans_rel: "trans R"
begin
end


locale proset = transitive + 
  assumes refl_rel:"refl_on (carrier R) R"
begin

abbreviation (input) "the_ordering \<equiv> R"


abbreviation leq  (infixr "\<preceq>" 40) where
 "leq x y \<equiv> (x, y) \<in> R"

lemma carrier_refl: "x \<in> carrier R \<longleftrightarrow> (x, x) \<in> R"
  apply (safe; clarsimp simp: carrier_def image_iff)
   apply (metis prod.collapse refl_onD refl_on_domain refl_rel)
  by (metis fst_conv)


end

locale poset = proset +
  assumes antisym: "x \<preceq> y \<Longrightarrow> y \<preceq> x \<Longrightarrow> x = y"


locale linset = poset +
  assumes complete: "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow>  x \<preceq> y \<or> y \<preceq> x"




locale semilattice = abel_semigroup + idemp_semigroup
begin



sublocale poset "{(x, y). x \<in> S \<and> y \<in> S \<and> times x y = y}"
  apply (standard)
    apply (rule transI; clarsimp)
  apply (metis assoc)
   apply (rule refl_onI; clarsimp simp: carrier_def)
    apply (intro conjI; clarsimp simp: image_iff)
    apply (blast)
    apply (intro conjI; clarsimp simp: image_iff)
    apply (elim disjE; clarsimp)
   apply (elim disjE; clarsimp simp: idemp)
  apply (clarsimp simp: idemp)
  using commute by force

lemma "S = carrier {(x, y). x \<in> S \<and> y \<in> S \<and> times x y = y}"
  apply (clarsimp simp: carrier_def total_on carrier_def, safe; clarsimp simp: image_iff)
  by (metis closed fst_conv idemp)+


notation leq  (infixr "\<preceq>" 40)

lemma le_join:  "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<preceq> (times x y)"
  apply (clarsimp)
  by (simp add: assoc closed_times idemp)

lemma join_least:  " x \<preceq> z \<Longrightarrow> y \<preceq> z \<Longrightarrow> (times x y) \<preceq> z "
  apply (clarsimp)
  by (metis closed_times assoc)

end

locale lattice = join: pis _ lub +  semilattice _ lub _ + meet: pis _ glb + dual: semilattice _ glb _ 
  for  lub :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<squnion>" 70) and 
       glb :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<sqinter>" 70) +
     assumes meet_join: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> glb x y = x \<longleftrightarrow> lub x y = y" 

begin


lemma "leq y x \<Longrightarrow> z \<in> S \<Longrightarrow> dual.leq x (y \<sqinter> z)"
  apply (clarsimp)  
  by (metis dual.assoc  dual.closed_times dual.commute meet_join)

end


interpretation set_lattice: lattice "UNIV \<times> UNIV" "UNIV" "(\<union>)" "(\<inter>)"
  apply (standard; (clarsimp intro!: refl_onI symI simp: carrier_def Un_commute Un_assoc)?)
        apply force+
       apply (rule refl_onI; clarsimp)
    apply force+
  done

lemma set_eqD: "S = S' \<Longrightarrow> \<forall>x. x \<in> S \<longleftrightarrow> x \<in> S'"
  by blast


lemma set_noteq_disj:"S \<noteq> S' \<Longrightarrow> (\<exists>x. x \<in> S' \<and> x \<notin> S) \<or> (\<exists>x. x \<notin> S' \<and> x \<in> S)"
  apply (blast)
  done


definition "restrict R S = R - (S \<times> UNIV)"

definition "project R S = R - (UNIV \<times> S)"


abbreviation (input) "to_rel f \<equiv> {(x, y). y = f x} "


lemma insert_ssubsetD: "x \<notin> F \<Longrightarrow> insert x F \<subset> R \<Longrightarrow> F \<subset> R - {x}" 
  apply (safe; clarsimp)
  apply blast
  done

lemma project_iff:"(a, b) \<in> project R S \<longleftrightarrow> (a, b) \<in> R \<and> b \<notin> S"
  by (safe; clarsimp simp: project_def)

lemma restrict_iff:"(a, b) \<in> restrict R S \<longleftrightarrow> (a, b) \<in> R \<and> a \<notin> S"
  by (safe; clarsimp simp: restrict_def)

lemma project_insert: "x \<notin> F \<Longrightarrow> insert x F \<subset> snd ` R \<Longrightarrow> F \<subset> snd ` (project R {x}) " 
  apply (frule (1) insert_ssubsetD)
  apply (erule psubset_subset_trans)
  apply (clarsimp simp: )
  apply (clarsimp simp:  image_iff Ball_def project_iff)
  apply blast
  done



end