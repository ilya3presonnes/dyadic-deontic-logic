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
abbreviation truthset :: "\<W> \<Rightarrow> \<R> \<Rightarrow> \<V> \<Rightarrow> \<P> \<Rightarrow> \<W>" ("(_,_,_)>\<parallel>_\<parallel>") = ("\<lambda>W::\<W>.\<lambda>R::\<R>.\<lambda>V::\<V>.\<lambda>p::\<P>.\<lambda>t::\<W>.\<langle>W,R,V\<rangle>,t \<Turnstile> p")
abbreviation bestset :: "\<W> \<Rightarrow> \<R> \<Rightarrow> \<V> \<Rightarrow> \<P> \<Rightarrow> \<W>" ("(_,_,_)>best(_)") = ("\<lambda>W::\<W>.\<lambda>R::\<R>.\<lambda>V::\<V>.\<lambda>p::\<P>.\<lambda>s::\<W>. \<langle>W,R,V\<rangle>,s \<Turnstile> p \<and> \<forall>t::\<W>. (\<langle>W,R,V\<rangle>,t \<Turnstile> p \<rightarrow> R s t)")
primrec TruthEvaluation :: "\<W>\<Rightarrow>\<succeq>\<Rightarrow>\<V>\<Rightarrow>w\<Rightarrow>DDL\<Rightarrow>bool" ("\<langle>_,_,_\<rangle>,_\<Turnstile>_") where 
  "\<langle>W,R,V\<rangle>,w \<Turnstile> P" = (V P w)
| "\<langle>W,R,V\<rangle>,w \<Turnstile> \<not>P" = (\<not>"\<langle>W,R,V\<rangle>,w \<Turnstile> P")
| "\<langle>W,R,V\<rangle>,w \<Turnstile> P \<rightarrow> Q" = ("\<langle>W,R,V\<rangle>,w \<Turnstile> P \<rightarrow> \<langle>W,R,V\<rangle>,w \<Turnstile> Q")
| "\<langle>W,R,V\<rangle>,w \<Turnstile> \<box>P" = ("\<forall>v:W. \<langle>W,R,V\<rangle>,v \<Turnstile> P")
| "\<langle>W,R,V\<rangle>,w \<Turnstile> \<circle>(P/Q)" = ("(W,R,V)>best(Q) \<rightarrow> (_,_,_)>\<parallel>P\<parallel>")
end
