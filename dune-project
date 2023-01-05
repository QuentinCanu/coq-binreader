(lang dune 3.0)

(using coq 0.3)

(wrapped_executables false)

(name coq-binreader)

(generate_opam_files true)

(package
 (name coq-binreader)
 (depends
  (ocaml (>= 4.08.0))
  (coq (and (>= 8.16) (< 8.17)))
  (coq-bignums (and (>= 8.16) (< 8.17))))
)
