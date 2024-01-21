# INF551 - Implementing a propositional prover

[Instructions by Samuel Mimram](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/4.prover.html)

This implementation has been made by [Clément CHAPOT](mailto:clement.chapot@polytechnique.edu)

To build provers, run `dune build` \
To run the (basic) prover, run `dune exec prover {log_file}` \
To run the dependent_prover, run `dune exec dependent_prover`

To verify a (basic) proof, run `cat proofs/{filename} | dune exec prover /dev/null` \
To verify a dependent proof, run `cat dependent_proofs/{filename} | dune exec prover`

Proofs made using prover.ml are located in `proofs/` \
Proofs made using dependent_prover.ml are located in `dependent_proofs/`
