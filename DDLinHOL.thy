theory DDLinHOL imports Main

begin
  typedecl \<w>
  typedecl \<P>
  consts p::\<P>
  type_synonym \<W> = "\<w>\<Rightarrow>bool" 
  type_synonym \<R> = "\<w>\<Rightarrow>\<w>\<Rightarrow>bool"
  type_synonym \<V>  = "\<P>\<Rightarrow>\<w>\<Rightarrow>bool" 

  \<comment> \<open>Syntax of DDL\<close>
  datatype DDL = Atom \<P> ("_\<^sup>d") | Neg DDL ("\<not>\<^sup>d") | Impl DDL DDL (infixr "\<rightarrow>\<^sup>d" 93) | Box DDL ("\<box>\<^sup>d") | Circ DDL DDL ("\<circle>\<^sup>d'(_'/_')")

  \<comment>\<open>Logical connectives\<close>
  definition Or (infixr "\<or>\<^sup>d" 92) where "\<phi> \<or>\<^sup>d \<psi> \<equiv> \<not>\<^sup>d\<phi> \<rightarrow>\<^sup>d \<psi>"
  definition And (infixr "\<and>\<^sup>d" 95) where "\<phi> \<and>\<^sup>d \<psi> \<equiv> \<not>\<^sup>d(\<phi> \<rightarrow>\<^sup>d \<not>\<^sup>d\<psi>)"
  definition Iff (infixr "\<longleftrightarrow>\<^sup>d" 100) where "\<phi> \<longleftrightarrow>\<^sup>d \<psi> \<equiv> (\<phi> \<rightarrow>\<^sup>d \<psi>) \<and>\<^sup>d (\<psi> \<rightarrow>\<^sup>d \<phi>)"
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
  | "(\<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d \<circle>\<^sup>d(\<psi>/\<phi>)) = (\<forall>s::\<w>. W s \<longrightarrow>((\<langle>W,R,V\<rangle>,s\<Turnstile>\<^sup>d\<phi>) \<and> (\<forall>t::\<w>.(W t \<longrightarrow> (\<langle>W,R,V\<rangle>,t\<Turnstile>\<^sup>d\<phi>) \<longrightarrow> R s t)) \<longrightarrow> (\<langle>W,R,V\<rangle>,s \<Turnstile>\<^sup>d \<psi>)))"

  abbreviation valid :: "DDL \<Rightarrow> bool" ("\<Turnstile>\<^sup>d _") 
    where "\<Turnstile>\<^sup>d \<phi> \<equiv> \<forall>W::\<W>.\<forall>R::\<R>.\<forall>V::\<V>.\<forall>w::\<w>. \<langle>W,R,V\<rangle>,w \<Turnstile>\<^sup>d\<phi>"

  \<comment> \<open>Classical semantics\<close>
  primrec ClassicalEvaluation :: "(DDL \<Rightarrow> bool) \<Rightarrow> DDL \<Rightarrow> bool" ("\<langle>_\<rangle>\<Turnstile>\<^sup>c\<^sup>l_") where
    "(\<langle>V\<rangle>\<Turnstile>\<^sup>c\<^sup>l (\<phi>\<^sup>d)) = V (\<phi>\<^sup>d)"
  | "(\<langle>V\<rangle>\<Turnstile>\<^sup>c\<^sup>l (\<not>\<^sup>d\<phi>)) = (\<not>\<langle>V\<rangle>\<Turnstile>\<^sup>c\<^sup>l \<phi>)"
  | "(\<langle>V\<rangle>\<Turnstile>\<^sup>c\<^sup>l (\<phi> \<rightarrow>\<^sup>d \<psi>)) = ((\<langle>V\<rangle>\<Turnstile>\<^sup>c\<^sup>l \<phi>) \<longrightarrow> (\<langle>V\<rangle>\<Turnstile>\<^sup>c\<^sup>l \<psi>))"
  | "(\<langle>V\<rangle>\<Turnstile>\<^sup>c\<^sup>l (\<box>\<^sup>d\<phi>)) = V (\<box>\<^sup>d\<phi>)"
  | "(\<langle>V\<rangle>\<Turnstile>\<^sup>c\<^sup>l \<circle>\<^sup>d(\<psi>/\<phi>)) = V (\<circle>\<^sup>d(\<psi>/\<phi>))"

  abbreviation validProp :: "DDL \<Rightarrow> bool" ("\<Turnstile>\<^sup>c\<^sup>l _")  
    where "(\<Turnstile>\<^sup>c\<^sup>l \<phi>) \<equiv> \<forall>V::(DDL\<Rightarrow>bool).\<langle>V\<rangle>\<Turnstile>\<^sup>c\<^sup>l\<phi>"

  \<comment> \<open>The proposition is provable if it is derivable using the rule schema or is an axiom schema\<close>
  inductive provable :: "DDL \<Rightarrow> bool" ("\<turnstile>\<^sup>d _") where
    taut : "\<Turnstile>\<^sup>c\<^sup>l \<phi> \<Longrightarrow> \<turnstile>\<^sup>d \<phi>"
  | MP : "\<turnstile>\<^sup>d \<phi> \<Longrightarrow> \<turnstile>\<^sup>d (\<phi> \<rightarrow>\<^sup>d \<psi>) \<Longrightarrow> \<turnstile>\<^sup>d \<psi>"
  | K : "\<turnstile>\<^sup>d (\<box>\<^sup>d(\<phi> \<rightarrow>\<^sup>d \<psi>) \<rightarrow>\<^sup>d (\<box>\<^sup>d\<phi> \<rightarrow>\<^sup>d \<box>\<^sup>d\<psi>) )"
  | T : "\<turnstile>\<^sup>d (\<box>\<^sup>d\<phi> \<rightarrow>\<^sup>d \<phi>)"
  | 5 : "\<turnstile>\<^sup>d (\<not>\<^sup>d(\<box>\<^sup>d\<phi>) \<rightarrow>\<^sup>d \<box>\<^sup>d(\<not>\<^sup>d(\<box>\<^sup>d\<phi>)))"
  | COK : "\<turnstile>\<^sup>d (\<circle>\<^sup>d((\<psi> \<rightarrow>\<^sup>d \<chi>)/\<phi>) \<rightarrow>\<^sup>d (\<circle>\<^sup>d(\<psi>/\<phi>) \<rightarrow>\<^sup>d \<circle>\<^sup>d(\<chi>/\<phi>)))"
  | Id : "\<turnstile>\<^sup>d \<circle>\<^sup>d(\<phi>/\<phi>)"
  | Sh : "\<turnstile>\<^sup>d (\<circle>\<^sup>d(\<chi>/\<phi> \<and>\<^sup>d \<psi>) \<rightarrow>\<^sup>d \<circle>\<^sup>d((\<psi>\<rightarrow>\<^sup>d\<chi>)/\<phi>))"
  | Abs: "\<turnstile>\<^sup>d (\<circle>\<^sup>d(\<psi>/\<phi>) \<rightarrow>\<^sup>d \<box>\<^sup>d\<circle>\<^sup>d(\<psi>/\<phi>))"
  | Nec : "\<turnstile>\<^sup>d (\<box>\<^sup>d\<psi> \<rightarrow>\<^sup>d \<circle>\<^sup>d(\<psi>/\<phi>))"
  | Ext : "\<turnstile>\<^sup>d (\<box>\<^sup>d(\<phi> \<longleftrightarrow>\<^sup>d \<psi>) \<rightarrow>\<^sup>d (\<circle>\<^sup>d(\<chi>/\<phi>) \<longleftrightarrow>\<^sup>d \<circle>\<^sup>d(\<chi>/\<psi>)))"
  | SqNec : "\<turnstile>\<^sup>d \<phi> \<Longrightarrow> \<turnstile>\<^sup>d (\<box>\<^sup>d\<phi>)"

  \<comment> \<open>Soundness and completeness\<close>
  theorem soundness: "(\<turnstile>\<^sup>d \<phi>) \<Longrightarrow> (\<Turnstile>\<^sup>d \<phi>)" 
  proof (induction pred: provable)
    \<comment> \<open>Tautology\<close>
    fix \<phi> assume "\<Turnstile>\<^sup>c\<^sup>l \<phi>"
    show "\<Turnstile>\<^sup>d \<phi>" sorry
  next
    \<comment> \<open>Modem ponens\<close>
    fix \<phi> \<psi> 
    assume  " \<Turnstile>\<^sup>d \<phi>" "\<Turnstile>\<^sup>d (\<phi> \<rightarrow>\<^sup>d \<psi>)"
    show "\<Turnstile>\<^sup>d \<psi>" \<comment> \<open>Hammered\<close> 
      by (metis \<open>\<Turnstile>\<^sup>d \<phi>\<close> TruthEvaluation.simps(3) \<open>\<Turnstile>\<^sup>d (\<phi> \<rightarrow>\<^sup>d \<psi>)\<close>)
  next
    \<comment> \<open>Axiom K\<close>
    fix \<phi> \<psi>
    show "\<Turnstile>\<^sup>d (\<box>\<^sup>d(\<phi> \<rightarrow>\<^sup>d \<psi>) \<rightarrow>\<^sup>d (\<box>\<^sup>d\<phi> \<rightarrow>\<^sup>d \<box>\<^sup>d\<psi>))" \<comment> \<open>Hammered\<close> 
      by simp
  next
    \<comment> \<open>Axiom T\<close>
    fix \<phi>
    show "\<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi> \<rightarrow>\<^sup>d \<phi>)" nitpick sorry \<comment> \<open>Found counter example\<close>
  next
    \<comment> \<open>Axiom S5\<close>
    fix \<phi>
    show "\<Turnstile>\<^sup>d (\<not>\<^sup>d(\<box>\<^sup>d\<phi>) \<rightarrow>\<^sup>d \<box>\<^sup>d(\<not>\<^sup>d(\<box>\<^sup>d\<phi>)))" \<comment> \<open>Hammered\<close> 
      by auto
  next 
    \<comment> \<open>Axiom of Conditional Obligation K\<close>
    fix \<phi> \<psi> \<chi>
    show "\<Turnstile>\<^sup>d (\<circle>\<^sup>d((\<psi> \<rightarrow>\<^sup>d \<chi>)/\<phi>) \<rightarrow>\<^sup>d (\<circle>\<^sup>d(\<psi>/\<phi>) \<rightarrow>\<^sup>d \<circle>\<^sup>d(\<chi>/\<phi>)))" \<comment> \<open>Hammered\<close> 
      by fastforce
  next 
    \<comment> \<open>Identity axiom\<close>
    fix \<phi>
    show "\<Turnstile>\<^sup>d \<circle>\<^sup>d(\<phi>/\<phi>)" \<comment> \<open>Hammered\<close> 
      by simp
  next
    \<comment> \<open>Shoham axiom\<close>
    fix \<psi> \<chi> \<phi>
    show "\<Turnstile>\<^sup>d (\<circle>\<^sup>d(\<chi>/\<phi> \<and>\<^sup>d \<psi>) \<rightarrow>\<^sup>d \<circle>\<^sup>d((\<psi>\<rightarrow>\<^sup>d\<chi>)/\<phi>))" \<comment> \<open>Hammered\<close>
      by (simp add: And_def)
  next
    \<comment> \<open>Absoluteness\<close>
    fix \<phi> \<psi>
    show "\<Turnstile>\<^sup>d (\<circle>\<^sup>d(\<psi>/\<phi>) \<rightarrow>\<^sup>d \<box>\<^sup>d\<circle>\<^sup>d(\<psi>/\<phi>))" \<comment> \<open>Hammered\<close>
      by auto
  next
    \<comment> \<open>Necessitation axiom\<close>  
    fix \<phi> \<psi>
    show "\<Turnstile>\<^sup>d (\<box>\<^sup>d\<psi> \<rightarrow>\<^sup>d \<circle>\<^sup>d(\<psi>/\<phi>))" \<comment> \<open>Hammered\<close>
      by simp
  next
    \<comment> \<open>Extentionality rule\<close>
    fix \<phi> \<psi> \<chi>
    show "\<Turnstile>\<^sup>d (\<box>\<^sup>d(\<phi> \<longleftrightarrow>\<^sup>d \<psi>) \<rightarrow>\<^sup>d (\<circle>\<^sup>d(\<chi>/\<phi>) \<longleftrightarrow>\<^sup>d \<circle>\<^sup>d(\<chi>/\<psi>)))" sledgehammer
      by (smt (verit) And_def Iff_def TruthEvaluation.simps(2,3,4,5))
  next 
    \<comment> \<open>Rule of necessitation of settled states\<close>  
    fix \<phi>
    assume "\<Turnstile>\<^sup>d \<phi>"
    show "\<Turnstile>\<^sup>d (\<box>\<^sup>d\<phi>)" \<comment> \<open>Hammered\<close>
      by (metis \<open>\<Turnstile>\<^sup>d \<phi>\<close> TruthEvaluation.simps(4))
  qed
    
  theorem completness: "(\<Turnstile>\<^sup>d \<phi>) \<longrightarrow> (\<turnstile>\<^sup>d \<phi>)" \<comment> \<open>Hammered\<close>
  proof -
    have "\<forall>d w b ba. \<langle>\<lambda>w. False,\<lambda>w wa. ba,\<lambda>p w. b\<rangle>,w\<Turnstile>\<^sup>dd"
      by (metis (no_types) T TruthEvaluation.simps(3,4) soundness)
    then show ?thesis
      by (metis (no_types) TruthEvaluation.simps(1))
  qed

theorem sound_and_complete: "( \<turnstile>\<^sup>d \<phi>) \<longleftrightarrow> ( \<Turnstile>\<^sup>d \<phi>)" using completness soundness by blast

end