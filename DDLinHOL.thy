theory DDLinHOL
imports Main  
begin
  typedecl \<w> 
  typedecl \<P>
  consts p::\<P>
  type_synonym \<W> = "\<w>\<Rightarrow>bool" 
  type_synonym \<R> = "\<w>\<Rightarrow>\<w>\<Rightarrow>bool"
  type_synonym \<succeq> = \<R>
  type_synonym \<V>  = "\<P>\<Rightarrow>\<w>\<Rightarrow>bool" 
\<comment>\<open>Relation properties\<close>
  abbreviation(input) "reflexive \<equiv> \<lambda>R::\<R>. \<forall>x. R x x"
  abbreviation(input) "symmetric \<equiv> \<lambda>R::\<R>. \<forall>x y. R x y \<longrightarrow> R y x"
  abbreviation(input) "transitive       \<equiv> \<lambda>R::\<R>. \<forall>x y z. (R x y \<and> R y z)  \<longrightarrow> R x z"

datatype DDL = Atom \<P> ("_") | Neg DDL ("\<not>") | Impl DDL DDL (infixr "\<rightarrow>" 93) | Box DDL ("\<box>") | Circ DDL DDL ("\<circle>'(_/_')")
\<comment>\<open>Logical connectives\<close>
definition Or (infixr "\<or>" 92) where "\<phi> \<or> \<psi> \<equiv> \<not>\<phi> \<rightarrow> \<psi>"
definition And (infixr "\<and>" 95) where "\<phi> \<and> \<psi> \<equiv> \<not>(\<phi> \<rightarrow> \<not>\<psi>)"
definition Dia ("\<diamond>_") where "\<diamond>\<phi> \<equiv> \<not>(\<box>(\<not>\<phi>))"
definition Prob ("P(_/_)") where "P(\<psi>/\<phi>) \<equiv> \<not>\<circle>(\<not>\<psi>/\<phi>)"
definition Top ("\<top>")  where  "\<top> \<equiv> p \<rightarrow> p"
definition Bot ("\<bottom>") where "\<bottom> \<equiv> \<not>\<top>"
definition Obl ("\<circle>_") where "\<circle>\<phi> \<equiv> \<circle>(\<phi>/\<top>)"
definition Mbe ("P_") where "P\<phi> \<equiv> P(\<phi>/\<top>)"
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
