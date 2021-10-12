(lang dune 2.8)

(name lcheck)

(version dev)

(generate_opam_files true)

(source
 (uri "git+https://github.com/jmid/lcheck.git"))

(bug_reports "https://github.com/jmid/lcheck/issues")

(homepage "https://github.com/jmid/lcheck")

(authors "Jan Midtgaard <mail@janmidtgaard.dk>")

(maintainers "Jan Midtgaard <mail@janmidtgaard.dk>")

(package
 (name lcheck)
 (synopsis "LCheck is a module for quickchecking lattice-based code")
 (depends
  (dune :build)
  qcheck))
