theory DDLinHOL
imports Main  
begin
  typedecl \<w>
  typedecl \<P>
  consts p::\<P>
  type_synonym \<W> = "\<w>\<Rightarrow>bool" 
  type_synonym \<R> = "\<w>\<Rightarrow>\<w>\<Rightarrow>bool"
  type_synonym \<V>  = "\<P>\<Rightarrow>\<w>\<Rightarrow>bool" 
  \<comment>\<open>Relation properties\<close>
  abbreviation(input) "reflexive \<equiv> \<lambda>R::\<R>. \<forall>x. R x x"
  abbreviation(input) "symmetric \<equiv> \<lambda>R::\<R>. \<forall>x y. R x y \<longrightarrow> R y x"
  abbreviation(input) "transitive       \<equiv> \<lambda>R::\<R>. \<forall>x y z. (R x y \<and> R y z)  \<longrightarrow> R x z"

  datatype A = Nil | Cons 

  datatype DDL = Atom \<P> ("_\<^sup>d") | Neg DDL ("\<not>\<^sup>d") | Impl DDL DDL (infixr "\<rightarrow>\<^sup>d" 93) | Box DDL ("\<box>\<^sup>d") | Circ DDL DDL ("\<circle>\<^sup>d'(_'/_')")
  \<comment>\<open>Logical connectives\<close>
  definition Or (infixr "\<or>\<^sup>d" 92) where "\<phi> \<or>\<^sup>d \<psi> \<equiv> \<not>\<^sup>d\<phi> \<rightarrow>\<^sup>d \<psi>"
  definition And (infixr "\<and>\<^sup>d" 95) where "\<phi> \<and>\<^sup>d \<psi> \<equiv> \<not>\<^sup>d(\<phi> \<rightarrow>\<^sup>d \<not>\<^sup>d\<psi>)"
  definition Dia ("\<diamond>\<^sup>d_") where "\<diamond>\<^sup>d\<phi> \<equiv> \<not>\<^sup>d(\<box>\<^sup>d(\<not>\<^sup>d\<phi>))"
  definition Perm ("P\<^sup>d'(_'/_')") where "P\<^sup>d(\<psi>/\<phi>) \<equiv>  \<circle>\<^sup>d(\<not>\<^sup>d\<psi>/\<phi>)"
  definition Top ("\<top>\<^sup>d")  where  "\<top>\<^sup>d \<equiv> (p\<^sup>d \<rightarrow>\<^sup>d (p\<^sup>d))"
  definition Bot ("\<bottom>\<^sup>d") where "\<bottom>\<^sup>d \<equiv> \<not>\<^sup>d(\<top>\<^sup>d)"
  definition Obl ("\<circle>\<^sup>d_") where "\<circle>\<^sup>d\<phi> \<equiv> \<circle>\<^sup>d(\<phi>/\<top>\<^sup>d)"
  definition Pos ("P\<^sup>d_") where "P\<^sup>d\<phi> \<equiv> P\<^sup>d(\<phi>/\<top>\<^sup>d)"
  \<comment>\<open>Semantic logic\<close>
  primrec TruthEvaluation :: "\<W>\<Rightarrow>\<R>\<Rightarrow>\<V>\<Rightarrow>\<w>\<Rightarrow>DDL\<Rightarrow>bool" ("\<langle>_,_,_\<rangle>,_\<Turnstile>\<^sup>d_") where 
  \<comment> \<open>Relational semantics\<close>
    "(\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<phi>\<^sup>d)) = (V \<phi> w)"
  | "(\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<not>\<^sup>d\<phi>)) = (\<not>\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi>)"
  | "(\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<psi> \<rightarrow>\<^sup>d \<phi>)) = ((\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<psi>) \<longrightarrow> (\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi>))"
  \<comment> \<open>Preference semantics\<close>
  | "(\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>)) = (\<forall>t::\<w>.((W t = True) \<longrightarrow> \<langle>W,R,V\<rangle>,t \<Turnstile>\<^sup>d \<phi>))"
  \<comment> \<open>Here the we quantify over all worlds, not over the world set W. Should we switch it?\<close>
  | "(\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<circle>\<^sup>d(\<psi>/\<phi>)) = (\<forall>s::\<w>.((\<langle>W,R,V\<rangle>,s\<Turnstile>\<^sup>d\<phi>) \<and> (\<forall>t::\<w>.((\<langle>W,R,V\<rangle>,t\<Turnstile>\<^sup>d\<phi>) \<longrightarrow> R s t)) \<longrightarrow> (\<langle>W,R,V\<rangle>,s \<Turnstile>\<^sup>d \<psi>)))"
end
