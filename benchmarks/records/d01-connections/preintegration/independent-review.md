# Independent D01 mathematical review

Result: no material findings in the frozen mathematical sources reviewed.

Reviewer: `/root/independent_review`, an independent agent that did not author D01 implementation files.
Reviewed repository: `/workspace/ref-type`, branch `math/d01-connections`.
HEAD at final reread: `d80c1ac5ac08d5553f2f00adab75754c047e4b03`.
Reviewed 375 package mathematical source/manifest files by source inventory; key constructions and proof chains were read substantively as listed below.
The SHA256 of the sorted JSON `(repository-relative path, file SHA256)` mathematical inventory is `ce5bfd601174e890c1a24c27539526e0dd8dcdaf0eb225a6d29d93f85d0e078c`. This identifies the review inputs even if the final evidence-only commit differs.

## Scope and conclusions

- Read `AGENTS.md`, the full original `_plans/math/d01-connections.md` requirements before completion deletion (preserved at checkpoint `5dac284141bf65a94992fa8a76f41dcd3a03e349`), package API documentation, registration and dependent roadmap links.
- Traced actual real connection existence through weighted pure-gauge terms, support-zero extension, smoothness, locally finite sums, affine cocycle and normalization; the empty index case is handled separately.
- Traced complex existence through actual bundle realification, constant J, projection `(A-JAJ)/2`, transition commutation and J-preserving connection data. This is a proved construction rather than an existence premise.
- Read positive-metric inverse construction through the existing Gram algorithm and smooth inverse theorem, metric correction and its naturality, plus the Hermitian real-part/J construction.
- Read raised Koszul coefficients, torsion and compatibility laws, local uniqueness, actual Jacobian/Hessian coordinate transformation, restriction, and native tangent-bundle Levi–Civita gluing/uniqueness. The coordinate hypotheses used by generic lemmas are discharged by actual native chart/metric proofs.
- Traced real and complex dual/tensor/exterior constructors to native B07 bundle fibers and transition matrices. The final complex tensor and exterior constructors use extracted complex coefficients, proved representation gauge laws, and `FromCoefficients` to construct actual global connections. Their `coefficients` comparisons recover the constructed local data. Realification and complex tensor ranks are distinguished.
- Read global compatible bundle-valued form families, their actual tensor-section construction, global d∇ descent, real linearity, graded scalar wedge Leibniz, degree-zero section comparison, and complex J/complex-scalar commutation. The documentation accurately states that `ValuedForms` uses compatible chart families and provides a forward native-section conversion.
- Final reread covered actual global pullback forms and d∇ naturality: chart pullbacks are proved compatible on the actual refined pullback bundle, and `Valued.Naturality.law` follows from the proved local naturality on every pulled frame.
- Checked the documented zero-rank, nonzero rank-one, flat and Euclidean Levi–Civita examples and the updated completion/dependency links.

No desired theorem was found hidden as an axiom or merely supplied as an existence hypothesis. Ordinary hypotheses of generic algebra/coordinate lemmas are instantiated by proved native constructions. No material mathematical or scope defect was found.

## Verification boundary

This was a read-only substantive source review; the reviewer ran no checker process. The final reread inspected accepted report outcomes for `induced-tensor-full-2.report.json`, `induced-exterior-full-2.report.json`, `global-forms-resume3.report.json`, and `global-valued-pullback2.report.json` under `/workspace/d01-resume-evidence`. These reports refer to their own fixed snapshots. Final fixed-source package, regression and whole-repository validation remain the root agent's separate required evidence.
