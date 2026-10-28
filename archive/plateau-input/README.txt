SELF-SIMILAR COUNTEREXAMPLES TO LORENTZ'S CONSECUTIVE-DEGREE CONJECTURES
October 28, 2026

RESULTS

The accompanying proof constructs two continuous functions on [-1,1].

1. A function f_o with f_o(0)=0 and P_(2k+1) f_o = P_(2k+2) f_o for every
   k>=0, although f_o is not odd.

2. A function f_e with P_(2k) f_e = P_(2k+1) f_e for every k>=0, although
   f_e is not even.

P_n denotes the unique best uniform approximating polynomial of degree at
most n. These are Conjectures 3' and 4 in Saff--Varga, Journal of
Approximation Theory 30 (1980), 29--36.

Both functions are self-similar series with contraction -3/5. The explicit
perturbation size epsilon=10^-10 is justified by the analytic bounds and
the exact coefficient checks. The first forcing has degree seven; the
second has degree eight. The approximate decimal coefficients in the
paper are for orientation: exact algebraic definitions are essential.

PROOF STATUS

The package contains a complete analytic proof and exact algebraic
certificates. The new constructions have NOT been formalized in Lean.
The previously completed Lean proof of the common-origin-zero
counterexample is a different result and is not included here.

The finite certificates have each been checked twice, with independent
exact-arithmetic implementations. The independent audits use only the
Python standard library. No floating-point tolerance is used to accept
any identity or inequality. Floating-point numbers are printed only as
readable summaries.

The finite checks alone do not establish a uniform bound between contacts;
that step is supplied by the quantitative whole-interval stability
proposition in the paper. The auditors verify its exact coefficient and
epsilon hypotheses.

FILES

lorentz_plateau_counterexamples.pdf : complete proof (also supplied separately)
lorentz_plateau_counterexamples.tex : LaTeX source
odd_certificate.json               : exact algebraic certificate for 3'
even_certificate.json              : exact algebraic certificate for 4
audit_odd.py                       : independent standard-library audit
audit_even.py                      : independent standard-library audit
verify_odd.py                      : standard-library generator/checker for 3'
generate_even.py                   : optional FLINT generator/checker for 4
verification.txt                   : actual output of the independent audits
even_generation.log                : actual exact-generation output for 4
SHA256SUMS.txt                     : file hashes for the deliverable

VERIFY

From this directory, run:

    python3 audit_odd.py
    python3 audit_even.py

No additional Python package is required. Either audit accepts an
optional path to its JSON certificate as its first command-line argument.
The default path is the certificate next to the script, so the scripts can
also be invoked from another working directory.

REGENERATE THE EXACT DATA (OPTIONAL)

    python3 verify_odd.py

The even generator uses python-flint for fast exact algebraic elimination:

    python3 -m pip install python-flint
    python3 generate_even.py

The independent audit of its output does not use FLINT. The supplied
certificate is sufficient to verify the result without installing FLINT.

REBUILD THE DOCUMENT

    pdflatex lorentz_plateau_counterexamples.tex
    pdflatex lorentz_plateau_counterexamples.tex

The source uses ordinary AMS LaTeX, geometry, microtype, booktabs,
mathtools, and hyperref. The final document was rendered and visually
reviewed.
