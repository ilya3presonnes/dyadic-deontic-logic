theory DDLinHOL
imports Main  
begin
  typedecl \<w> 
  typedecl \<P>
  consts p::\<P> q::\<P> 
  type_synonym \<W> = "\<w>\<Rightarrow>bool" 
  type_synonym \<R> = "\<w>\<Rightarrow>\<w>\<Rightarrow>bool" 
  type_synonym \<V>  = "\<P>\<Rightarrow>\<w>\<Rightarrow>bool" 
\<comment>\<open>Properties of relations\<close>
  abbreviation(input) "reflexive        \<equiv> \<lambda>R::\<R>. \<forall>x. R x x"
  abbreviation(input) "symmetric     \<equiv> \<lambda>R::\<R>. \<forall>x y. R x y \<longrightarrow> R y x"
  abbreviation(input) "transitive       \<equiv> \<lambda>R::\<R>. \<forall>x y z. (R x y \<and> R y z)  \<longrightarrow> R x z"
  abbreviation(input) "equivrel         \<equiv> \<lambda>R::\<R>. reflexive R \<and> symmetric R \<and> transitive R"
  abbreviation(input) "irreflexive      \<equiv> \<lambda>R::\<R>. \<forall>x. \<not>R x x" 
  abbreviation(input) "euclidean       \<equiv> \<lambda>R::\<R>. \<forall>x y z. R x y \<and> R x z \<longrightarrow> R y z"
  abbreviation(input) "wellfounded   \<equiv> \<lambda>R::\<R>. \<forall>P::\<W>. (\<forall>x. (\<forall>y. R y x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow>  (\<forall>x. P x)" 
  abbreviation(input) "converserel    \<equiv> \<lambda>R::\<R>. \<lambda>y. \<lambda>x. R x y" 
abbreviation(input) "conversewf    \<equiv> \<lambda>R::\<R>. wellfounded (converserel R)"


\<comment>\<open>Bounded universal quantifier: \<open>\<forall>x:W. \<phi>\<close> stands for \<open>\<forall>x. W x \<longrightarrow> \<phi> x\<close>\<close>
  abbreviation(input) "BAll W \<phi> \<equiv> \<forall>x::\<w>. W x \<longrightarrow> \<phi> x" syntax "BAll"::"pttrn\<Rightarrow>\<W>\<Rightarrow>bool\<Rightarrow>bool" ("(3\<forall>(_/:_)./_)" [0,0,10]10)
translations "\<forall>x:W. \<phi>" \<rightleftharpoons> "CONST BAll W (\<lambda>x. \<phi>)"

  \<comment>\<open>Deep embedding (of propositional modal logic in HOL)\<close>
datatype DDL = Atom \<P>  ("_") | Neg DDL ("\<not>") | Impl DDL DDL (infixr "\<rightarrow>" 93) | Box DDL ("\<box>") | Circ DDL DDL ("\<circle>'(_/_')")
\<comment>\<open>Further logical connectives as definitions\<close>
definition Or (infixr "\<or>" 92) where "\<phi> \<or> \<psi> \<equiv> \<not>\<phi> \<rightarrow> \<psi>"
definition And (infixr "\<and>" 95) where "\<phi> \<and> \<psi> \<equiv> \<not>(\<phi> \<rightarrow> \<not>\<psi>)"
definition Dia ("\<diamond>_") where "\<diamond>\<phi> \<equiv> \<not>(\<box>(\<not>\<phi>))"
definition Prob ("P(_/_)") where "P(\<psi>/\<phi>) \<equiv> \<not>\<circle>()"
definition Top ("\<top>")  where  "\<top> \<equiv> p \<rightarrow> p"
definition Bot ("\<bottom>") where "\<bottom> \<equiv> \<not>\<top>"
definition Obl ("\<circle>_") where "\<circle>\<phi> \<equiv> \<circle>(\<phi>/\<top>)"
definition 
\<comment>\<open>Definition of truth of a formula relative to a model \<open>\<langle>W,R,V\<rangle>\<close> and a possible world w\<close>
  primrec RelativeTruthD :: "\<W>\<Rightarrow>\<R>\<Rightarrow>\<V> \<Rightarrow>\<w>\<Rightarrow>PML\<Rightarrow>bool" ("\<langle>_,_,_\<rangle>,_  \<Turnstile>\<^sup>d _") where
       "\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d a\<^sup>d          = (V a w)"   
     | "\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<not>\<^sup>d\<phi>       = (\<not> \<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<phi>)"
     | "\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<phi> \<supset>\<^sup>d \<psi>   = (\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<phi>  \<longrightarrow>  \<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<psi>)"
     | "\<langle>W,R,V\<rangle>, w \<Turnstile>\<^sup>d \<box>\<^sup>d\<phi>       = (\<forall>v:W. R w v \<longrightarrow> \<langle>W,R,V\<rangle>, v \<Turnstile>\<^sup>d \<phi>)"
\<comment>\<open>Definition of validity\<close>
  definition ValD ("\<Turnstile>\<^sup>d _") where "(\<Turnstile>\<^sup>d \<phi>) \<equiv> (\<forall>W R V. \<forall>w:W. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<phi>)"
\<comment>\<open>Collection of definitions in a bag called DefD\<close>
end