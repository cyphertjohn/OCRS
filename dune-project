(lang dune 3.0)
(using menhir 2.1)
(name OCRS)

(generate_opam_files true)

(license MIT)
(authors "John Cyphert")
(maintainers "github.com/cyphertjohn")
(homepage "github.com/cyphertjohn/OCRS")
(bug_reports "github.com/cyphertjohn/OCRS")

(package
 (name OCRS)
 (synopsis "Recurrence solver based on operational calculus")
 (description "A package based on Lothar Berg's operational calculus to solve recurrences")
 (depends ocaml dune gmp)
 )

