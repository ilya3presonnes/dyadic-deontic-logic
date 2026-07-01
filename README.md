# About the project
<!-- TODO: add links to the papers -->
This project contains deep embbedding of deontic dyadic logic for conditional normative reasoning following [The LogiKey framework by Benzmüller et al.]. The embedding is done in theorem prover **Isabelle/HOL**, to follow the LogiKey framework, however embedding in Lean is also considered. 

## Project code of conduct
Please use the informative style for commit messages: 

- The headline containing the tag, describing the type of change commit brings
	* `feat:` used for new blocks of code, funciton, datatypes, definition, etc. For addition of proofs use the nest tag
	* `proof:` used when new proof or work on new proof is done. 
	* `fix:` used when commit introduces fixed to code or proofs
	* `refactor:` changing the existing code, with minimal new features, only changing the previous logic
	* `style:` used when commit changes the visual of code (indendation/blokcs). Mostly used when no refactoring happened, and signifies that the commit can be ignored, no logic or real changes are introduced. If any other changes (new definitions, renames, etc.) happen, use rafactor tag  
	* `docs:` used when editing documentation in code, or changing `README`, papers
- The commit body after a line separating head from body. The body contains the summary of changes, their nuances and reasons why changes where needed
- Optional footer, also with a line separating then. Footer should contain tags, however no tags exists on this moment. 

# Roadmap
- [x] Implement DDL syntax via an inductive type
- [x] Implement preference semantics with optimal set via an eliminationa and computation rules
- [ ] Implement preference semantics with maximal set via an eliminationa and computation rules
- [x] Implement proof system either as lemmas or as axioms (I am not sure if lemmas can be used in this case)
- [ ] Prove equivalence of shallow and deep embeddings 
- [ ] Port the embedding to Lean

## Use of Lean
Lean is another theorem prover, known for its use in formalistion of mathematics. Where as Isabelle/HOL's approach is inspired by LCF (Logic for Computable Functions), Lean's approach is use of dependent type theory and the proposition as types approach (which is the clearest instance of Curry-Howard Isomorphism).

However, given that the simplicity of Lean in relation to its logical kernel, and both HOL and Lean being in pure functional programming styles, the port of the embedding to Lean is pretty straight forward.

## How Isabelle works
TODO: Write about the programming foundation of Isabelle - ML, about the Logics for computable functions and Isabelle/Pure. Write a section about implementation of inductive definitions using bounded functors, as I use inductive definition for the formalisation

## Potential advancements
- It could be nice to provide another semantics,based on maximimal notion of the betterness relation
