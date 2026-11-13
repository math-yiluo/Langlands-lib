# Division-case Harris CM representability: Library reductions, open obligations and Anthropic FLT resources

Worker 3269, 10 November 2026, updated 13 November 2026, executor of Task 3269
(`6eac742d-7f56-403d-8f08-f535a1ca289c`). This note maps the current Library
work toward
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.DivisionCMRepresentabilityStatement`.
It also lists results in the registered Anthropic FLT Lean source that bear on
the open steps. It is a planning and navigation note. It accepts no external
proof and asserts no unproved theorem.

## The exact obligation

The target is in `Langlands/Shimura/PEL/HarrisTaylorCMDivisionRepresentabilityStatement.lean`.
It is `D.IsDivision → CMRepresentabilityStatement D C …`. The consequent is in
`HarrisTaylorCMRepresentabilityStatement.lean`. It asks for the following at
every object `U` of `SmallCMLevel D`:

- an object `base` of `ComponentwiseAdmissibleCMBaseCategory`;
- `Smooth base.obj.hom`;
- `IsHProjective base.obj.hom`, a closed immersion into polynomial-Proj
  projective space over `F` that commutes with the structure maps;
- a natural isomorphism `uliftYoneda.{1}.obj base ≅ (smallLevelClassPresheafTower …).obj U`.

### No degenerate shortcut

The following checks were made on the definitions.

- The Harris signature charts are compatible with the division hypothesis.
- Sufficiently small levels exist. `LevelSufficientlySmall` requires only that
  finite-order elements of the projection to one `G(ℚ_p)` be trivial.
- `GroupScheme.Tate.Index P` is `{n // 0 < n ∧ P n}`. The `torsionUnits`
  field of `AdmissibleCMBase` therefore says only that the base has
  characteristic zero.
- The empty scheme lies in the test category, and the presheaf has the
  singleton empty-product value there. Nonempty schemes are admissible
  exactly when Worker 147's dual-geometry characterization holds (see below).
- The moduli definitions are faithful. They use actual abelian schemes,
  polarizations through the Library dual, Rosati compatibility, the normalized
  determinant condition, relative dimension `[E:ℚ]·n²`, the central Lie trace,
  monodromy-invariant adelic level orbits and the rational-isogeny quotient.

The target is therefore the genuine theorem of Kottwitz, *Points on some
Shimura varieties over finite fields* (1992), §5, printed pp.389–392, in
characteristic zero. Source: `kottwitz-1992-points-shimura-finite-fields`.
p.391 proves representability relative to Mumford's moduli space, using
Hilbert schemes of endomorphisms, and proves smoothness over
`𝒪_E ⊗ ℤ_(p)` by Grothendieck–Messing deformation theory. p.392 proves
projectivity when `End_B(V)` is a division algebra. That proof uses Néron
models, Grothendieck's semistable reduction theorem and Mumford's index theory.

## Reductions already in the Library

All of these are internal constructions. Unless stated otherwise they are in
`Langlands/Shimura/PEL/`.

| Module(s) | Content |
| --- | --- |
| `HarrisTaylorCMIntegralExistence`, `HarrisTaylorCMIntegralPresheafComparison` | Every normalized class has integral representatives. `integralCMDisconnectedClassPresheafIso` identifies the integral-image presheaf with the full one. These take the generic `ProperFibreAmpleAffineOpenStatement`, now proved as `properFibreAmpleAffineOpen`. |
| `HarrisTaylorCMOrdinaryPresheaf` (with `…OrdinaryClasses`, `…OrdinaryIsomorphisms` and `HarrisTaylorCMTate*`) | Worker 344. At levels `U` with `(lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C`, the ordinary presheaf `tateNormalizedCMOrdinaryDisconnectedPresheaf` consists of actual-isomorphism classes of integral normalized models. `tateNormalizedCMOrdinaryDisconnectedIso` compares it with the original CM presheaf. Its two generic inputs are `ProperFibreAmpleAffineOpenStatement` and `Tate.CommensurableInvariantLatticeRealizationStatement`; both are now proved. |
| `HarrisIntegralCMRosatiLocus`, `…EquationLocus`, `…ActionLocus`, `…FullActionLocus`, `…ClosedActionLocus`, `HarrisIntegralActionDeterminantLocus` | Closed loci of integral-order actions satisfying the Rosati equations and the normalized determinant, over a supplied abelian family with a supplied relative-End representative. |
| `HarrisProjectiveCMActionScheme` | For an `IsHProjective` abelian scheme over a noetherian affine `Spec R`, it constructs the closed CM action scheme, its universal action and the natural classification. No module uses it yet. |
| `HarrisIntegralCMLevel*`, especially the `OrbitCover` modules | Level structures on an integral-action family are classified by actual finite étale "orbit covers". These use `geometricContinuousActionEquivalence` and cover disconnected tests. |
| `HarrisTaylorCMBaseAdmissibility` | Worker 147. `componentwiseAdmissibleCMBase_iff_dualGeometry` characterizes admissibility. `componentwiseAdmissibleCMBase_of_relativeDual` derives it from `RelativeDualSchemeExistenceStatement` and `RelativeDualSchemeGeometryStatement`. |
| `HarrisTaylorCMDivisionAssembly` | Worker 3269, published 13 November 2026. `CMLevelGeometricRepresentation U` is the data a quasi-projective construction produces: a scheme over `Spec F`, possibly not admissible, that is smooth and proper, with an immersion into `ℙ^m_F` over `F` and a natural isomorphism `admissibleTestPoints X ≅ (smallLevelClassPresheafTower …).obj U` on the admissible test category. `CMGeometricRepresentabilityStatement` asks for this data at every small level. Under `RelativeDualSchemeExistenceStatement` and `RelativeDualSchemeGeometryStatement`, `cmRepresentabilityStatement_iff_geometric` shows it is equivalent to the exact `CMRepresentabilityStatement`. `divisionCMRepresentabilityStatement_of_geometric` derives the target from those two statements and `D.IsDivision → CMGeometricRepresentabilityStatement …`. Two generic helpers are added in namespace `Langlands.AlgebraicGeometry`. `IsHProjective.of_isImmersion_of_isProper` says that proper plus an immersion into `ℙ^m_R` over `Spec R` gives `IsHProjective`. `IsHProjective.exists_isImmersion` is the converse. |
| `Langlands.RingTheory.Smooth.ArtinianLifting` (file `Langlands/RingTheory/Smooth/ArtinianLifting.lean`, namespace `Langlands.RingTheory.ArtinianLifting`) | `Langlands.RingTheory.ArtinianLifting.smooth`: if `C` is noetherian, `S` is a finite-type `C`-algebra and `HasArtinianLifting C S` holds, then `Algebra.Smooth C S`. `HasArtinianLifting C S` asks for lifts of `C`-algebra maps `ψ : S → B` along every surjection `φ : B' → B` of local Artinian `C`-algebras with `maximalIdeal B' * ker φ = ⊥`, but only for `ψ` whose composite with the residue map of `B` is surjective. Finite type is essential: a polynomial algebra in infinitely many variables over a field has the lifting property but is not finitely presented. |

Two of the inputs are delegated to other tasks.

- Task 3449, `ce5bb036-afaa-497b-b2ca-ee75e40fcacb`, a child of this target,
  proves `PolarizedFiniteLevel.LargeLevelRepresentabilityStatement`. That is
  eventual fine representability of the ordinary full-level functor over
  `ℤ[1/n]` (Mumford–Fogarty–Kirwan, Theorem 7.9). The cubic-bundle modules in
  `Langlands/AbelianScheme/PolarizedFiniteLevel/` serve it.
- The two relative dual statements are the subject of many Picard proof
  tasks. Examples are `522d3c86-486f-49bb-8fc1-68a353b0fdd5` (geometry),
  `cb1ffcd6-3094-4950-b2a3-b3a058361f63` (universal Picard-zero family),
  `f39b40a8-68f7-4734-a60f-bca1f46f648c` (properness),
  `b6a7f057-6bd6-4d77-ab24-9b79698666f8` (flatness) and
  `54d4a7cc-7607-4c5a-82e7-25bafba9e3e9` (valuative existence). On
  10 November 2026 the relative existence and geometry tasks, and the field
  existence task `f38215ec-58a9-488f-8fd0-305952a3db2b`, were waiting under an
  explicit operator pause; see the next section. On 13 November 2026 Task 3449
  and the relative existence task `cb1ffcd6-…` were waiting with no
  artifacts. The relative geometry task `522d3c86-…` was running. It had
  staged a statement reducing relative geometry to field smoothness, relative
  flatness and relative local finite presentation of the dual.

## Open obligations with no proof owner (task searches of 10 November 2026)

1. **PEL locus over the ordinary moduli.** Apply the projective CM action
   scheme to the universal family over the ordinary moduli scheme base-changed
   to `F`. This needs relative projectivity of that universal family over
   affine opens, gluing of the closed loci, and the full-level-to-Harris-level
   comparison through the orbit covers.
2. **Finite quotients.** A small level need not lie inside a lattice-stabilizing
   principal congruence level. Representability at a general small `U`
   therefore needs a quotient by a finite group acting freely, and its
   quasi-projectivity.
3. **Smoothness.** This is deformation theory of PEL data. In characteristic
   zero it is the Hodge-filtration (Grothendieck–Messing) argument. On an
   integral model it is Serre–Tate together with Grothendieck–Messing, or
   Lubin–Tate theory at a prime split in `L` as in Harris–Taylor III.4.
4. **Division-case properness.** The steps are the valuative criterion,
   potentially good reduction (semistable reduction, plus the
   `D.eq_zero_of_finrank_lt` dimension obstruction already published in
   `Langlands.Shimura.Unitary.DivisionCondition`), Néron extension of the
   polarization, action and level. The final passage from proper and
   quasi-projective to `IsHProjective` is now
   `IsHProjective.of_isImmersion_of_isProper`.
5. **Assembly.** This is now partly published in `HarrisTaylorCMDivisionAssembly`.
   Admissibility of the representer and transport of the representing
   isomorphism from the restricted functor of points to `uliftYoneda` are done
   there, conditional on the two relative dual statements. What remains is to
   produce `CMLevelGeometricRepresentation` at each small level. That means
   combining the ordinary presheaf comparison with a smooth proper
   quasi-projective scheme over `F` from obligations 1–4. The representer need
   not be shown admissible in that step. See the next section for the relative
   dual statements.

## Blocking dependency: admissibility needs relative duals

The representing object must lie in `ComponentwiseAdmissibleCMBaseCategory`.
Each connected component must then satisfy `AdmissibleCMBase`
(`HarrisTaylorCMPolarizedUnpointedPresheaf.lean`). Its field `dualExists`
asks for `Nonempty (DualEvaluationData preservation stability B)` for every
`B : AbelianScheme` over that component. `DualEvaluationData`
(`HarrisPolarizedClassBaseChange.lean`) contains `hasDual : HasDualScheme B`
and `geometry : DualSchemeGeometry B hasDual`. By Worker 147's
`nonempty_dualEvaluationData_iff` and
`componentwiseAdmissibleCMBase_iff_dualGeometry`, admissibility of a locally
noetherian base is equivalent to `CMBaseDualGeometry` on each component
scheme: every abelian scheme over it has an actual dual with the stated
geometry.

The empty scheme lies in the test category, since it has no components. It
represents the presheaf only if the presheaf is empty on every nonempty object
of the test category. Otherwise the representer is nonempty, and a proof of
the target must establish dual existence and geometry for every abelian scheme
over each of its components, with no such premise. This is the content of `RelativeDualSchemeExistenceStatement` and
`RelativeDualSchemeGeometryStatement` over those components. As noted above,
their proof tasks were under an operator pause on 10 November 2026; their
13 November status is given there. `HarrisTaylorCMDivisionAssembly` takes
both statements as explicit hypotheses, so it isolates this dependency from the
construction of the representing scheme. The
ordinary moduli child, Task 3449, meets the same gap: a `PolarizedFiniteLevel`
datum carries a dual witness, so its universal datum needs an actual dual of
the universal abelian scheme.

## Anthropic FLT resources

Registered source: `anthropic-flt-complete-lean-source-6e837e75`, at
`literature/Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2/`.
It is licensed Apache-2.0. Lean 4.33.1 was used there, while the project uses
Lean 4.34.0 and Mathlib `5ed2965`. About 1466 of its modules are already
ported under `Langlands/AnthropicFLT/`. The theorem names below are the FLT
names. "Closure" counts the distinct source modules, including the theorem's
own module, reached by following every import that resolves to a file of the
source tree (its `Theorems`, `Definitions` and `P2M` directories). Imports of
Lean and Mathlib are not counted. "Ported" counts those closure modules
already present in the Library.

| FLT theorem | Content | Closure / ported |
| --- | --- | --- |
| `AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_quasiProjective` (`Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_thetaTypeLocally_quasiProjective.lean`, lines 41–51) | Fine moduli of `g`-dimensional polarized abelian schemes with polarization locally of theta type `δ` and full level `n ≥ 3`, over any commutative ring `𝒪` in which `n` and the degree `∏ δ_i` are units. The scheme is separated, quasi-compact, locally of finite presentation and quasi-projective, and every finite set of points lies in an affine open. Tests are affine. | 3936 / 1101 |
| `AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_finite_represents_of_isUnit_two_of_finiteType` (`Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_finite_represents_of_isUnit_two_of_finiteType.lean`, lines 38–68) | Only for polarized abelian schemes of dimension 2 (`PolarisedAbelianScheme 2 d m R`) over a finite-type `ℤ`-algebra `R` in which `2` and the full level `m ≥ 3` are units. The quaternion algebra is a specified indefinite one over `ℚ` ramified exactly at two distinct primes `q, q'`, with a maximal order `Λ`, an element `μ ∈ Λ` with `μ² = -qq'`, a map `star : Λ → Λ` with `μ · star x = x̄ · μ` for the quaternion conjugate `x̄`, and a `ℤ`-basis `β` of `Λ`. Under these hypotheses, `Λ`-structures on the family are represented by a finite, locally finitely presented scheme over `Spec R`. | 6591 / 1355 |
| `CerednikDrinfeld.QM.exists_isFineModuli_of_isUnit_two_of_isUnit_three` (`Theorems/Thm_CerednikDrinfeld_QM_exists_isFineModuli_of_isUnit_two_of_isUnit_three.lean`, lines 41–54) | Fine moduli of QM abelian surfaces ("fake elliptic curves") for the same kind of quaternion algebra (indefinite over `ℚ`, ramified exactly at distinct primes `q, q'`, maximal order `Λ`), with level `N` and full level `m ≥ 3`, over a commutative ring `𝒪` in which `N`, `m`, `2` and `3` are units. The scheme is separated, quasi-compact and locally of finite type, and is smooth of relative dimension 1 when `qq'` is also a unit. It is a division-case PEL instance of dimension 2 only. | 7887 / 1355 |
| `CerednikDrinfeld.QM.IsFineModuli.isProper_of_isUnit_two_of_isUnit_three` (`Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_isProper_of_isUnit_two_of_isUnit_three.lean`, lines 42–52) | Properness of any fine moduli scheme for that problem, over a characteristic-zero domain `𝒪` in which `N`, `m`, `2` and `3` are units. | 8788 / 1423 |
| `AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift` (`Theorems/Thm_AlgebraicGeometry_universallyClosed_of_forall_isDiscreteValuationRing_isAdicComplete_finite_residueField_hasLift.lean`, lines 12–17) | Universal closedness from lifts over complete DVRs with finite residue field, for quasi-compact morphisms locally of finite type to `Spec B`, `B` a finite-type `ℤ`-algebra. | 32 / 17 |
| `AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int` (`Theorems/Thm_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int.lean`, lines 9–18) | Two separate finite-type hypotheses: `R` is a finite-type `ℤ`-algebra, and the morphism `ϖ : M → Spec R` is locally of finite type. Under both, `ϖ` is smooth if it lifts along every surjection `T' → T` with `T'` local Artinian, residue field algebraically closed of prime characteristic, and kernel annihilated by the maximal ideal of `T'`. Without local finite type of `ϖ` the conclusion fails: `Spec 𝔽_p[x_1, x_2, …] → Spec 𝔽_p` has all these lifts but is not smooth. | 43 / 0 |
| `AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation`, `…exists_fppf_quotient_of_forall_exists_quotient_restrict`, `…exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj` | Quotients by finite locally free equivalence relations, and quasi-projectivity of finite quotients. | not computed |
| `AlgebraicGeometry.DescentAction.effective_of_finiteEtale_of_forall_orbit` | Effectivity of finite étale descent under an affine-orbit hypothesis. | not computed |

The FLT QM proofs are integral. Smoothness is reduced to closed points of a
finite-type `ℤ`-scheme, which have finite residue fields, and is proved by
characteristic-`p` deformation along Artinian thickenings
(`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_of_sq_eq_bot_of_isArtinianRing`).
Properness uses the complete-DVR criterion above together with extension of
QM abelian surfaces over such DVRs. Neither argument is a general PEL theorem.
The FLT objects are not the Library's. FLT's `PolarisedAbelianScheme` uses a
`RelativeGroupLaw` on affine bases and a relatively very ample line bundle. The
Library uses `AbelianScheme` (a commutative group object over the base) and
polarizations into the Library dual. Reusing the FLT moduli would therefore
need a definitional bridge, in addition to the port.

## Route assessment

- The characteristic-zero route, over `F` directly, needs a de Rham or
  Hodge-filtration deformation theory. It also needs good reduction over
  discrete valuation rings with characteristic-zero residue field. Neither is
  present in the Library or in the FLT source.
- The integral route mirrors Kottwitz §5, Harris–Taylor III.4 and the FLT
  Shimura-curve construction. One builds a smooth proper model over a
  finite-type `ℤ`-algebra in `F`, then base-changes to `F`. The FLT
  characteristic-`p` smoothness and complete-DVR properness criteria apply to
  this route. It adds an integral PEL moduli problem with prime-to-`p`
  isogenies, and its comparison with the rational normalized presheaf.
- Under either route, obligations 1, 2 and 5 are characteristic-zero Library
  work. They depend only on Task 3449, the relative dual statements and the
  existing reductions. Both of those inputs currently wait on the paused
  Picard program.

This note records the state on 10 November 2026. The assembly module and the
status of the blocking tasks were updated on 13 November 2026. Check the current Library
and task list before relying on the ownership statements above.
