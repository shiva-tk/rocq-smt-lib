(lang dune 3.13)
(using coq 0.8)
(name rocq-smt-lib)

(generate_opam_files true)
(license MIT)
(source (github shiva-tk/rocq-smt-lib))

(package
  (name rocq-smt-lib)
  (synopsis "Rocq mechanisation of SMT-LIB")
  (description "A mechanisation of the logical semantics of version 2.7 of the SMT-LIB standard")
  (tags
    ("logpath:SMTLIB"
     "category:Computer Science/Semantics and Compilation/Semantics"
     "keyword:SMT-LIB"
     "keyword:SMT"))
  (depends
    (rocq-core (and (>= 9.0) (< 9.3~)))
    (rocq-stdlib (and (>= 9.0) (< 9.3~)))
    (rocq-stdpp (>= 1.13.0))
    (coq-hammer-tactics (>= 1.3.2))
    (rocq-equations (>= 1.3.1))
  )
  (maintainers
    "Shiva Tamil Kumaran"
    "Andreas Lööw"
  )
  (authors
    "Shiva Tamil Kumaran"
  )
)
