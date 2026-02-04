(lang dune 3.20)

(name heft)

(generate_opam_files true)

(source
 (github bord-o/heft))

(authors "Brody Little <brodylittle011@gmail.com>")

(maintainers "Brody Little <brodylittle011@gmail.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name heft)
 (synopsis "interactive theorem proving with algebraic effects")
 (description "applying algebraic effects to a HOL tactic system for composable tactics and ergonomic proof search")
 (depends ocaml ppx_here ppx_deriving ppx_expect sexplib utop multicont ocamlformat sedlex)
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
