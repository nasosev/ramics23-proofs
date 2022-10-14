theory Example
imports Information_Algebras
begin


(* Example *)

locale example = 
  fixes "a" :: 'var and b :: "'var" and a0 :: "'val" and a1 :: "'val" and b0 :: "'val" and b1 :: "'val" 
  assumes distinct_variables[simp]: "a \<noteq> b"
  assumes distinct_values_a[simp]: "a0 \<noteq> a1" 
  assumes distinct_values_b[simp]: "b0 \<noteq> b1" 

begin

lemma distinct_variables'[simp]: "b \<noteq> a" by (clarsimp, drule sym, clarsimp)

lemma distinct_values_a'[simp]: "a1 \<noteq> a0" by (clarsimp, drule sym, clarsimp)

lemma distinct_values_b'[simp]: "b1 \<noteq> b0" by (clarsimp, drule sym, clarsimp)

definition V :: "'var set"
  where "V = {a, b}"

definition V_opens :: "'var set set" 
  where "V_opens = {{a}, {b}, {a,b}, {}}"

lemma V_opens_simps[simp]: "{a} \<in> V_opens"  "{b} \<in> V_opens"  "{a, b} \<in> V_opens"  "{} \<in> V_opens"
  by (clarsimp simp: V_opens_def)+

sublocale  topological_space V_opens V
  apply (standard; clarsimp simp: V_opens_def V_def)
    apply (blast)
   apply (blast)
  by (blast)

definition Omega_a :: "'val rel"
  where "Omega_a = {(a0, a0), (a0, a1), (a1, a1)}"

definition Omega_b :: "'val rel"
  where "Omega_b = {(b0, b0), (b0, b1), (b1, b1)}"

(* Mapping from variables to prosets *)

definition Omega :: "'var \<Rightarrow> ('val rel) "
  where "Omega v = (if v = a then (Omega_a) else if v = b then Omega_b else undefined)"

lemma Omega_simps[simp]:  "Omega a = {(a0, a0), (a0, a1), (a1, a1)}" by (clarsimp simp: Omega_def Omega_a_def)

lemma Omega_simps'[simp]: "Omega b =  {(b0, b0), (b0, b1), (b1, b1)}" by (clarsimp simp: Omega_def Omega_b_def)

sublocale Omega V_opens V Omega
  apply (standard)
   apply (rule transI; clarsimp simp: V_def Omega_b_def Omega_def Omega_a_def split: if_splits)
    apply (blast)
  apply (blast)
  apply (rule refl_onI)
   apply (clarsimp simp: V_def Omega_b_def Omega_def Omega_a_def  carrier_def split: if_splits )
  by (clarsimp simp: V_def Omega_b_def Omega_def Omega_a_def  carrier_def split: if_splits)




definition t :: "('var \<times> 'val) set list "
  where "t = [{(a, a0), (b, b0)}, {(a, a1), (b, b0)}, {(a, a1), (b, b1)}]"


definition t' :: "('var \<times> 'val) set list "
  where "t' = [{(a, a0), (b, b0)}, {(a, a1), (b, b1)}]"

lemma carrier_insert_simp[simp]: "carrier (insert (x,y) S) = {x, y} \<union> carrier S"
  by (clarsimp simp: carrier_def, safe)

lemma t_is_trace_of_chaos: "(t) \<in> \<Union>(snd ` chaos ` V_opens)"
  apply (clarsimp simp: image_iff chaos_def)
  apply (rule_tac x="{a,b}" in bexI)
   apply (clarsimp simp: chaos_obj_def nondegen_def)
   apply (intro conjI)
    apply (rule_tac x="length t" in exI)
    apply (clarsimp simp: nerve_obj_def)
    apply (clarsimp simp: t_def)
    apply (rule cons_step)
     apply (rule cons_step)
      apply (rule single)
      apply (clarsimp simp: carrier_om_iff single_valued_def)
     apply (clarsimp simp: om_iff single_valued_def)
  apply (clarsimp simp: om_iff single_valued_def)
   apply (clarsimp simp: distinct_adj_def t_def)
   apply (simp add: doubleton_eq_iff)
  apply (clarsimp simp: V_opens_def)
  done


lemma t'_is_trace_of_chaos: "(t') \<in> \<Union>(snd ` chaos ` V_opens)"
  apply (clarsimp simp: image_iff chaos_def)
  apply (rule_tac x="{a,b}" in bexI)
   apply (clarsimp simp: chaos_obj_def nondegen_def)
   apply (intro conjI)
    apply (rule_tac x="length t'" in exI)
    apply (clarsimp simp: nerve_obj_def)
    apply (clarsimp simp: t'_def)
    apply (rule cons_step)
     apply (rule single) 
     apply (clarsimp simp: carrier_om_iff single_valued_def)
     apply (clarsimp simp: om_iff single_valued_def)
   apply (clarsimp simp: distinct_adj_def t'_def)
   apply (simp add: doubleton_eq_iff)
  apply (clarsimp simp: V_opens_def)
  done


definition U :: "'var set"
  where "U = {a}"

lemma [simp]: "ax \<in> {a0, a1} \<Longrightarrow> bx \<in> {b0, b1} \<Longrightarrow> rest ({a}, {a, b}) $ {(a, ax), (b, bx)} = {(a, ax)}"
  apply (intro set_eqI iffI; clarsimp)
    apply (subst (asm) apply_iff)
      apply (clarsimp simp: single_valued_def rest_def)
     apply (clarsimp simp: rest_def)
     apply (intro conjI)
      apply (clarsimp simp:  carrier_om_iff)
     apply (clarsimp simp: single_valued_def)
  apply (blast)
     apply (rule refl)
    apply (clarsimp simp: restrict_iff)
   apply (subst  apply_iff)
     apply (clarsimp simp: single_valued_def rest_def)
    apply (clarsimp simp: rest_def carrier_om_iff)
    apply (intro conjI)
      apply (clarsimp simp: single_valued_def)
     apply (blast)
  apply (blast)
    apply (rule refl)
  by (clarsimp simp: restrict_iff)

lemma restrict_t_to_U: "down (({a, b}, {t}), U) = ({a}, {[{(a, a0)}, {(a, a1)}]})" 
  apply (clarsimp simp: down_def chaos_fun'_def )
  apply (safe; clarsimp simp: U_def)
  apply (clarsimp simp: chaos_obj_def nondegen_def)
    apply (clarsimp simp: chaos_fun_def mapf_def)
    apply (subst t_def, clarsimp)
 apply (clarsimp simp: chaos_obj_def nondegen_def)
   apply (intro conjI)
    apply (rule_tac x="length t" in exI)
    apply (clarsimp simp: nerve_obj_def)
    apply (clarsimp simp: t_def)
    apply (rule cons_step)
     apply (rule cons_step)
      apply (rule single)
      apply (subst carrier_om_iff, clarsimp simp: V_opens_def)
      apply (clarsimp simp: single_valued_def)
     apply (clarsimp simp: \<Omega>_def)
  apply (intro conjI; (clarsimp simp: single_valued_def)?)
   apply (clarsimp simp: \<Omega>_def)
  apply (intro conjI; (clarsimp simp: single_valued_def)?)
   apply (clarsimp simp: distinct_adj_def t_def)
   apply (simp add: doubleton_eq_iff)
  apply (clarsimp simp: chaos_fun_def relcomp.simps, clarsimp simp: mapf_def)
  apply (intro conjI)
   apply (clarsimp simp: rest_def image_iff)
   apply (clarsimp simp: carrier_om_iff)
   apply (intro conjI)
     apply (clarsimp simp: t_def, elim disjE; blast)
    apply (clarsimp simp: t_def single_valued_def)
    apply (elim disjE)
      apply auto[1]
  apply auto[1]
    apply auto[1]
   apply (clarsimp simp: t_def)
   apply (elim disjE; clarsimp, elim disjE; clarsimp simp: carrier_def Omega_def Omega_a_def Omega_b_def)
  apply (clarsimp simp: t_def)
  done

lemma restrict_t'_to_U: "down (({a, b}, {t'}), U) = ({a}, {[{(a, a0)}, {(a, a1)}]})" 
   apply (clarsimp simp: down_def chaos_fun'_def )
  apply (safe; clarsimp simp: U_def)
  apply (clarsimp simp: chaos_obj_def nondegen_def)
    apply (clarsimp simp: chaos_fun_def mapf_def)
    apply (subst t'_def, clarsimp)
 apply (clarsimp simp: chaos_obj_def nondegen_def)
   apply (intro conjI)
    apply (rule_tac x="length t'" in exI)
    apply (clarsimp simp: nerve_obj_def)
    apply (clarsimp simp: t'_def)
    apply (rule cons_step)
      apply (rule single)
      apply (subst carrier_om_iff, clarsimp simp: V_opens_def)
      apply (clarsimp simp: single_valued_def)
     apply (clarsimp simp: \<Omega>_def)
  apply (intro conjI; (clarsimp simp: single_valued_def)?)
   apply (clarsimp simp: distinct_adj_def t'_def)
   apply (simp add: doubleton_eq_iff)
  apply (clarsimp simp: chaos_fun_def relcomp.simps, clarsimp simp: mapf_def)
  apply (intro conjI)
   apply (clarsimp simp: rest_def image_iff)
   apply (clarsimp simp: carrier_om_iff)
   apply (intro conjI)
     apply (clarsimp simp: t'_def, elim disjE; blast)
    apply (clarsimp simp: t'_def single_valued_def)
    apply (elim disjE)
      apply auto[1]
  apply auto[1]
    apply auto[1]
   apply (clarsimp simp: t'_def)
   apply (elim disjE; clarsimp, elim disjE; clarsimp simp: carrier_def Omega_def Omega_a_def Omega_b_def)
  apply (clarsimp simp: t'_def)
  done


end

end