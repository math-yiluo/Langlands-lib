# Étale-cohomology premises of the cohomological branch: audit of the Stacks and FAG sheaf libraries

This report, dated 17–18 November 2026, is an audit for the
plan note `operator-external-inputs-plan-2026-11-16` (its Sections 4.1, 3.2 and
5.2–5.5). Section 2 gives the premises and their consumers, Sections 4 and 7
the Stacks repository, Section 5 the FAG repository, Section 6 generic base
change, Section 8 the co-import question and Section 9 the recommendation. The
evidence file `statements.md` gives the full statements: the Library's premises
and its number-field spreading theorems (Part A), Stacks (Part B) and FAG
(Part C). No port and no dependency was started. The Library proves none of the
premises of Section 2 (checked against the Library as it is now); it has since
taken in the two Stacks tiers as the copies `StacksCore/` and `StacksFrontier/`.

**Verdict.**

1. Neither library proves any premise in the form the Library states it. Each
   proves the geometric core of three of them: specialization for smooth proper
   morphisms (good reduction), finiteness for proper varieties over an
   algebraically closed field, and the limit argument behind Galois smoothness.
   Both are stated with their own coefficient categories, one universe above the
   Library's, and none of these theorems involves number fields, places or
   inertia groups. Both libraries also have inertia results that cover part of
   the step from specialization to inertia at a place (bridges B4 and F5).
   FAG also proves, over any base, that the cospecialization map of the higher
   direct images of a smooth proper morphism is bijective, and it supplies the
   morphism from `Spec B_Q` to the strict localization through which this map
   and its inertia-invariant specialization map can be taken at the same
   points. What remains there is to prove that the two maps agree, to identify
   the generic stalk equivariantly, and to compare the global inertia group with
   the Library's. Stacks also supplies, for the good-reduction and smoothness
   premises, spreading out of a smooth proper morphism, descent of one locally
   constant sheaf to a stage (0GL2), finite-stage descent of cohomology classes
   over any algebraic extension, and the change of coefficient universe for
   abelian étale cohomology (Sections 4.1–4.4). The smooth proper model over
   a ring of `S`-integers needs neither library: it is an assembly of the
   Library's own number-field spreading theorems (bridge B3). Both libraries'
   specialization theorems need coefficients killed by an integer that is a
   unit on the base. So the premise's finite module `M` over an arbitrary ring
   is moved to `ZMod (Nat.card M)`, and the theorem is applied on an open where
   `Nat.card M` is a unit. The finite set of places still depends only on the
   model (bridges B3 and F4).
   The bridges are listed in Section 4.4 for Stacks and
   Section 5.4 for FAG. The full statements on both sides are in the evidence
   file `statements.md`.
2. Neither library has Deligne's generic base change (SGA 4½, Th. finitude 1.9)
   over a base such as `Spec 𝒪_K[1/N]`. FAG proves two forms of it over an
   integral base of finite type over a field (Section 5.3): one for an open
   immersion with constructible coefficients, and one for a smooth, separated,
   quasi-compact morphism with finite locally constant coefficients. Neither
   form reaches number fields: an open of `Spec 𝒪_K` is not a scheme over a
   field, and over `Spec K` itself they say nothing about places. Stacks has only
   special cases (Section 4.4). The route does not need it (Section 6). Its premise,
   `GaloisCohomologyUnramifiedStatement`, has no Lean consumer. For Kottwitz's
   varieties, which are smooth and proper, the unramified statement follows from
   specialization for smooth proper morphisms. This requires first a model
   over one arithmetic open that carries every coefficient stage `A_r` at once.
   That uniform extension is an additional obligation, which neither library
   meets (bridges B3′ and F4).
3. **FAG alone can supply every premise the route needs** (Section 5.5), with
   the bridges of Section 5.4. Unlike Stacks, it has no Galois-equivariant `RΓ`
   for a scheme base-changed to a separable closure (we found none). For
   smoothness it offers two routes (bridge F3). The first goes through its
   limit theorem (Stacks 09YQ in FAG) and the Library's own action. FAG has
   every geometric ingredient of this route: the limit cone over the finite
   subextensions of an algebraic extension, 09YQ for `Sheaf.H` along that cone,
   and the composition rule for the pullback maps on `Sheaf.H`. What remains is
   to compare cohomology groups and actions with the Library's (bridges F1 and
   F2). The second goes through its stalk formula for higher direct images (Stacks 03Q9 in FAG),
   its lemmas on the strict henselization of a field, and its equivalence
   between étale sheaves on `Spec K` and discrete Galois modules. Once
   assembled, these make `Hⁿ(X_Ω, F)` the underlying group of a discrete Galois
   module, for `Ω` a separable closure (or the algebraic closure, after a
   transport). FAG does not show that this module's action is the geometric
   action. For an arbitrary algebraic extension only the first route applies.
   Neither theorem has a torsion hypothesis, so both routes
   serve the smoothness premises with arbitrary coefficients, among them the
   level-colimit statement, which has Lean consumers (Section 2.4).
4. Both libraries are on Lean 4.35.0 with Mathlib `56a0058`, and the Library is on
   Lean 4.34.0 with Mathlib `5ed2965`. On the Library's pin, a 318-module Stacks
   closure compiles after 30 recorded edits: 21 change only imports and 9 change
   proofs. A 467-module FAG closure fails with at least 346 errors in 70 modules,
   unedited. The full premise closures, about 17,900 Stacks modules and 7,275 FAG
   modules, were not compiled. The text scans of both premise closures find no
   `sorry`, no axiom declaration and no kernel bypass.
5. One module cannot import both libraries' closures. The two declare 332 of
   the same names, and for at least 113 of them Lean rejects the import whatever
   the statements (Section 8). The final theorem of the project imports both
   branches. Of the 7,275 modules in the FAG premise closure, all but 19 lie
   in the closure of the five FAG modules that Laumon's theorem needs (the Laumon
   roots, Section 5.6).
6. *Recommendation* (Section 9). If FAG becomes the sheaf library for Laumon's
   theorem, as the plan note proposes, take the premises from FAG as well: one
   sheaf library, as a dependency at a common pin, with the bridges of
   Section 5.4. Stacks then serves as a model for the missing Galois-equivariant
   `RΓ` and is not imported. Stacks is the better source for these premises only
   if FAG is not adopted, or with a renaming fork.

## 1. Pins, evidence and reproducibility

| Input | Exact identity |
| --- | --- |
| AxiomMath/Stacks | `https://github.com/AxiomMath/Stacks`, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b` (committed 2026-11-10; the head on 17 November 2026), registered literature `axiommath-stacks-c496df0` (the GitHub source archive at the pin, SHA-256 `486b8562ef869c010549440faf498768eacc127c7507dd63d69702df54fa845c`, extracted). Apache-2.0 (`LICENSE`). Lean `v4.35.0`, Mathlib `v4.35.0` = `56a005855ea17e0b0958f73ec801ae140b0a1679`. Tiers: `StacksCore` (reviewed upstream) and `StacksFrontier` (AI-written and marked unreviewed upstream); 64,215 Lean files, all in the module system. |
| formal-arithmetic-geometry/weil-conjectures (FAG) | commit `a25955cde4f85f67bef3149a6efc3efe20c22132`, registered literature `formal-arithmetic-geometry-weil-conjectures-a25955c`. Apache-2.0. Lean 4.35.0, Mathlib `56a0058` (Section 5.1). |
| Library compared | commit `fcb85a7ef43356fec01e6ccf1605f08568c08cb0`. At the later Library commits `8aede86c1ec386cf08cfb29e80ce3c58a3239cd8` and `f050c0b1b525624bc32c1e7c25a8d2841bb2d4e0`, the 24 Library files cited here are byte-identical, and each premise name occurs in the same set of `*.lean` files. |
| Lean environment for the compiles | Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435` |
| Plan note | registered literature `operator-external-inputs-plan-2026-11-16` |

Both upstream heads equalled these pins when the audit began, on 17 November
2026. Stacks was read in a full clone at the pin and in a
depth-1 checkout. The registered copy has the same tracked files as the clone.
Stacks file paths in this note are relative to its root; Section 4 omits a
common prefix, which it states. FAG was read in the registered copy and in the checkout. No external code was run outside the project's Lean service.

Evidence files, in [`etale-premises-sheaf-libraries-evidence/`](etale-premises-sheaf-libraries-evidence/):

- [`stacks-sample2-manifest.md`](etale-premises-sheaf-libraries-evidence/stacks-sample2-manifest.md):
  the 318 modules of the second Stacks compile, each with its original SHA-256
  and, where the file was edited, its adapted SHA-256, plus the aggregate hashes.
- [`stacks-sample2-edits.md`](etale-premises-sheaf-libraries-evidence/stacks-sample2-edits.md):
  the complete unified diff of the 30 edited files.
- [`fag-scan-report.md`](etale-premises-sheaf-libraries-evidence/fag-scan-report.md):
  the method of the FAG closures and scans, the closure table, every hit and
  `sorry` site, the 19 premise modules outside the Laumon closures, the
  closures of the twelve modules cited for statements C.5–C.9 and
  of the nine further cited modules, and the focused FAG compile with its 70 failed modules (Section 5.6).
- [`co-import-name-clashes.md`](etale-premises-sheaf-libraries-evidence/co-import-name-clashes.md):
  the 332 declaration names that both closures declare, with the modules on each
  side, Lean's rule for duplicate imports and the 113 certain clashes
  (Section 8).
- [`statements.md`](etale-premises-sheaf-libraries-evidence/statements.md):
  the full Lean text, copied from the pinned sources, of every Library premise
  discussed here with its variable block, of the Library definitions they use,
  and of every external theorem compared in Sections 4 and 5, each with the
  namespaces, variables and local instances in scope at its line.

These are development records. This note does not make any external
declaration Library mathematics.

## 2. The premises and their consumers (item 1)

All statements are at Library `fcb85a7e`. `galoisCohomologyRep (L := L) f R M n`
is `EtaleCohomologyAction.constantCohomologyRep R (galoisAut f) M n`
(`Langlands/Geometry/EtaleGaloisAction.lean:91`). It is the action of
`L ≃ₐ[K] L` on degree-`n` étale cohomology of `X ×_{Spec K} Spec L` with
constant coefficients `M`, through the second factor. It is computed with a
chosen injective resolution (`Langlands/Geometry/EtaleConstantCohomology.lean:78`).
The cohomology is `EtaleDerivedSections.cohomology X R n`, the right derived
functor `(Sheaf.Γ …).rightDerived n` on
`EtaleDerivedSections.ModuleSheaf X R := Sheaf X.smallEtaleTopology (ModuleCat.{u} R)`
(`Langlands/Geometry/EtaleDerivedSections.lean:28, 58`). The higher direct
images are `EtaleDerivedDirectImage.higherDirectImage`
(`Langlands/Geometry/EtaleDerivedDirectImage.lean:57`). The full declarations,
with their variable blocks and universes, are in Part A of
[`statements.md`](etale-premises-sheaf-libraries-evidence/statements.md).

### 2.1 The general premises

```lean
-- Langlands.Cohomology.EtaleGaloisSmooth (SGA 4 VII 5.8)
def GaloisCohomologySmoothStatement (K : Type u) [Field K] (L : Type u) [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [QuasiCompact f] [QuasiSeparated f]
    (R : Type u) [CommRing R] : Prop :=
  ∀ (M : ModuleCat.{u} R) (n : ℕ),
    Langlands.IsSmooth (galoisCohomologyRep (L := L) f R M n).ρ

-- Langlands.Cohomology.EtaleGaloisGoodReduction (SGA 4 XVI 2.2)
def GaloisCohomologyGoodReductionStatement (K : Type u) [Field K] [NumberField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IsProper f]
    (R : Type u) [CommRing R] : Prop :=
  ∃ S : Set (Global.FinitePlace K), S.Finite ∧
    ∀ (M : ModuleCat.{u} R) [Finite M] (n : ℕ) (v : Global.FinitePlace K), v ∉ S →
      ((Nat.card M : NumberField.RingOfIntegers K) ∉ v.asIdeal) →
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{u} R) v
        ((Rep.RepToAction R (Field.absoluteGaloisGroup K)).obj
          (galoisCohomologyRep (L := AlgebraicClosure K) f R M n))

-- Langlands.Cohomology.EtaleGaloisUnramified (SGA 4½ Th. finitude 1.9)
def GaloisCohomologyUnramifiedStatement (K : Type u) [Field K] [NumberField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [QuasiCompact f] (R : Type u) [CommRing R] : Prop :=
  ∀ (M : ModuleCat.{u} R) [Finite M] (n : ℕ),
    ∃ S : Set (Global.FinitePlace K), S.Finite ∧ ∀ v ∉ S,
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{u} R) v
        ((Rep.RepToAction R (Field.absoluteGaloisGroup K)).obj
          (galoisCohomologyRep (L := AlgebraicClosure K) f R M n))
```

`DecompositionGroupAction.IsUnramifiedAt` means that the inertia subgroup of the
absolute Galois group of the completion `K_v` acts trivially. That subgroup is
restricted to `Gal(K̄/K)` along Mathlib's chosen embedding of algebraic closures.

### 2.2 The premises on Kottwitz's varieties

Here `X_U` is a Shimura variety of level `U` over the CM field `F`, and `X̄_U`
is its base change to `F̄ = AlgebraicClosure F`. `B_r` is the `r`-th stage of
the torsion coefficient system on `X̄_U`, pulled back from a sheaf `A_r` on
`X_U`. The ring `Rcoeff = HarrisCoefficientIntegers K p : Type` is the
coefficient ring: the product of the rings of integers of the completions of
`K` at the places above the rational prime `p`. Multiplication by `m^r` is zero
on `B_r`, where `m : ℕ` and `m ≠ 0` (`HarrisCMCohomology/Statement.md`). All of
this is at universe 0
(`ModuleCat.{0} Rcoeff`). The Library proves that `X̄_U` is smooth and proper
over `F̄`: the instances are `cmGeometricOverTower_smooth`
(`Langlands/Shimura/PEL/HarrisTaylorCMGeometricCoefficients.lean:109`) and
`cmGeometricOverTower_isProper`
(`Langlands/Shimura/PEL/HarrisTaylorCMGeometricProjective.lean:139`).

| Statement (module `Langlands.Cohomology.…`) | Content (full Lean text in the module) | Source |
| --- | --- | --- |
| `HarrisCMCohomology.HarrisCMCohomologyFiniteStatement` | `∀ degree r, Finite ((cmHarrisGeometricCoefficientCohomologySystem … degree).obj r)`: every `H^d(X̄_U, B_r)` is finite | SGA 4 XIV 1.2 |
| `HarrisCMCohomology.HarrisCMGaloisCohomologySmoothStatement` | `∀ degree r, IsSmooth ((Rep.ActionToRep Rcoeff Galois).obj ((cmHarrisGeometricGaloisCohomologyAction … degree).obj r)).ρ`, where `Galois = F̄ ≃ₐ[F] F̄` | SGA 4 VII 5.8 |
| `HarrisCMCohomology.HarrisCMCohomologyStatements` | the conjunction of the two above | |
| `HarrisCMCohomologyUnramified.HarrisCMCohomologyUnramifiedStatement` | `∃ S : Set (Global.FinitePlace F), S.Finite ∧ ∀ degree r (w ∉ S), IsUnramifiedAt (ModuleCat.{0} Rcoeff) w ((cmHarrisGeometricGaloisCohomologyAction … degree).obj r)`; one `S` for all degrees and stages | SGA 4 XVI 2.2, after spreading out |
| `HarrisCMLevelGaloisSmooth.HarrisCMLevelGaloisSmoothStatement` | for `R : Type`, every `d` and every `M : ModuleSheaf (Spec F) R`, each class in the colimit over small CM levels of `H^d(X̄_U, p_U^* M)` is fixed by an open subgroup of `Galois` | SGA 4 VII 5.8, level by level |
| `HarrisCMPrimeToGaloisSmooth.HarrisCMPrimeToGaloisSmoothStatement` | the same over the prime-to-`m` levels | the same |

The table abbreviates. Each of these statements takes more than twenty
explicit arguments (the unitary data `D`, the charts `C`, a dozen Picard and
duality statements, `q`, and either the level `U` with `ρ`, `p`, `m`, `hm` or
the rigidity family with `criterion` and `R`), written as `…` above.
Their full text is in Sections A.2 and A.3 of
[`statements.md`](etale-premises-sheaf-libraries-evidence/statements.md).

The Library also has `HarrisCM{Level,Colimit,PrimeTo}InvariantsStatement`. These
are Hochschild–Serre-type statements about invariants under level groups, not
SGA inputs on étale cohomology, so this audit leaves them out.

### 2.3 Consumers

We searched every `*.lean` file of Library `fcb85a7e` for each name.

| Premise | Lean consumers |
| --- | --- |
| `HarrisCMGaloisCohomologySmoothStatement` | `Langlands/Shimura/PEL/HarrisTaylorCMAdicGaloisCohomology.lean` (`continuous_cmHarrisAdicAction`, `cmHarrisAdicContAction`, hypothesis `hsmooth`) and `HarrisTaylorCMEllAdicGaloisCohomology.lean` (`continuous_cmHarrisEllAdicAction`). These are the continuous `p`-adic and `ℓ`-adic representations on the limit over `r`. |
| `HarrisCMLevelGaloisSmoothStatement` | `Langlands/Shimura/PEL/HarrisTaylorCMFixedVectorGaloisRepresentation.lean`, `HarrisTaylorCMHeckeMultiplicityGaloisRepresentation.lean`, `HarrisTaylorCMMultiplicityGaloisRepresentation.lean` (hypothesis `hsmooth`: the Galois representations on fixed vectors, Hecke multiplicity spaces and multiplicity spaces) |
| `HarrisCMCohomologyUnramifiedStatement` | none by name. Its pointwise content is the hypothesis `hu : ∀ r, IsUnramifiedAt … ((cohomologyAction degree).obj r)` of `cmHarrisAdicCohomology_isUnramifiedAt` (`HarrisTaylorCMAdicGaloisCohomology.lean:186`), which the statement implies for every `w ∉ S`. |
| `GaloisCohomologySmoothStatement`, `GaloisCohomologyGoodReductionStatement`, `GaloisCohomologyUnramifiedStatement`, `HarrisCMCohomologyFiniteStatement`, `HarrisCMCohomologyStatements`, `HarrisCMPrimeToGaloisSmoothStatement` | none |

**The reduction of Harris's Theorem 1.2.** A reduction of Harris 1998,
Theorem 1.2 (cuspidal existence) to named geometric inputs should cite the
names above unchanged. Nothing here renames a premise.

### 2.4 The level-colimit smoothness statements

`HarrisCMLevelGaloisSmoothStatement` has Lean consumers (Section 2.3). It
differs from the other smoothness premises in its coefficients and in its
passage to the colimit over levels.

*Coefficients.* The ring is any `R : Type`, and `M` is any sheaf of `R`-modules
on the small étale site of `Spec F`, pulled back to `X̄_U` along
`X̄_U → Spec F`. There is no finiteness or torsion condition, and `M` need not
be constant. So neither `GaloisCohomologySmoothStatement` (constant
coefficients) nor `HarrisCMGaloisCohomologySmoothStatement` (the stages `B_r`)
implies it.

*From the colimit to one level.* The Library already reduces the statement to
single levels. This step needs no external theorem:

1. `cmSmallLevelCohomology_exists_level_class`
   (`Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelCohomology.lean:238`, under
   `Nonempty (SmallCMLevel D)`) writes every class `x` of the colimit as
   `ι_U y`, for one small level `U` and one class `y` in
   `H^d(X̄_U, p_U^* M)`. The case without small levels is separate.
2. `cmSmallLevelGaloisCohomology_ρ_ι_apply`
   (`Langlands/Shimura/PEL/HarrisTaylorCMSmallLevelGaloisCoefficients.lean:301`)
   says that `σ` sends `ι_U y` to `ι_U (g_σ^♯ y)`. Here `g_σ^♯` is
   `LevelTowerCohomology.projectionCohomologyMap` along the automorphism of
   `X̄_U` induced by `σ`: the pullback along it, followed by the comparison of
   the two inverse images of `M`. By `cmSmallLevelGaloisAut_hom_app`, this
   automorphism is `EtaleGaloisAction.baseChangeMap _ σ`, the same map that
   underlies `galoisAut` in the general premise.
3. So the statement follows once, for every small level `U`, degree `d` and
   class `y`, some open subgroup `V` of `Gal(F̄/F)` satisfies `g_σ^♯ y = y` for
   all `σ ∈ V`. This per-level statement is SGA 4 VII 5.8 for the
   quasi-compact quasi-separated `F`-scheme `X_U`, with coefficients pulled back
   from `Spec F`. The Library does not state it.

The prime-to-`m` statement has the same structure. Its action formula is
`cmPrimeToGaloisCohomology_ρ_ι_apply`
(`Langlands/Shimura/PEL/HarrisTaylorCMPrimeToGaloisCohomology.lean:322`). The
generic `RestrictedLevelTowerCohomology.exists_level_class`
(`Langlands/Shimura/RestrictedLevelTowerCohomology.lean:167`) gives
representatives when the index property is downward closed and holds for some
level. Sections 4.2 and 5.3 say how each library serves the per-level
statement. The full Lean text of the statements and lemmas used in this
section is in Sections A.3 and A.4 of
[`statements.md`](etale-premises-sheaf-libraries-evidence/statements.md).

## 3. Site, coefficients and universes in the three developments

| | Site | Coefficient category | Ring | Cohomology |
| --- | --- | --- | --- | --- |
| Library | `X.smallEtaleTopology`, `X : Scheme.{u}` | `ModuleCat.{u} R` | `R : Type u` | `(Sheaf.Γ …).rightDerived n` (Mathlib `Functor.rightDerived`) |
| Stacks | the same | `ModuleCat.{max (u+1) r} Λ` (`EtaleModules.{u,r} Λ X`, `StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleModuleDerivedFunctors.lean:137`); the theorems below fix `r = 0` | `Λ : Type` | `Functor.rightDerived` of the direct image and global sections; on `D⁺`, `rightDerivedFunctorPlus` |
| FAG | the same | `ModuleCat.{u+1} Λ` | `Λ : Type (u+1)` | homology of derived sections on `D`/`D⁺`, or `Ext (constSheaf Λ) F q` (Section 5.2) |

The site is the same in all three. In the coefficients, Stacks differs from the
Library only in the universe of the modules (`u + 1` against `u`). The Stacks
ring is in `Type`, so it covers the Library's statements with `R : Type u` only
for `u = 0`, or for a ring equivalent to one in `Type`. The Harris statements are
at universe 0, so this restriction does not affect them. FAG also raises the
universe of the ring.

## 4. AxiomMath/Stacks: theorems for each premise (item 2)

All paths are under `StacksFrontier/AlgebraicGeometry/EtaleCohomology/` at
`c496df0`, unless another root is given. Every theorem below is in
`StacksFrontier`, the unreviewed tier. Part B of
[`statements.md`](etale-premises-sheaf-libraries-evidence/statements.md) gives
the full Lean text of every declaration named in this section, with the
namespaces, section variables and local instances in scope.

### 4.1 Good reduction and the Harris unramified statement (SGA 4 XVI 2.1–2.3)

`Stacks.EtaleCohomology.isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper`,
tag `0GLI` (`SmoothProperHigherDirectImageLocallyConstant.lean:331`):

```lean
theorem isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] (Λ : Type) [CommRing Λ]
    [IsNoetherianRing Λ] (F : EtaleModules.{u, 0} Λ X)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.smallEtaleTopology Λ F)
    (htors : ∀ x : GeometricPoint X, ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ n.Coprime (ringChar x.residueField)) ∧
      ∀ a : (smallEtaleStalkAb x.hom).obj ((etaleModuleForget Λ X).obj F), n • a = 0)
    (i : ℕ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} S.smallEtaleTopology Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived i).obj F)
```

`AlgebraicGeometry.isIso_specializationMap_of_smooth_of_isProper_unconditional`
(namespace `AlgebraicGeometry`),
tag `0GKD` (`LocalAcyclicity/SmoothProperSpecializationUnconditional.lean:68`):

```lean
theorem isIso_specializationMap_of_smooth_of_isProper_unconditional (B : BigEtaleSite.{u})
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) [Smooth f]
    [IsProper f] (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hFlc : Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F)
    (hFtors : ∀ (x : GeometricPoint X) (a : (smallEtaleStalkAb x.hom).obj F),
      ∃ n : ℕ, 0 < n ∧
        (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧ n • a = 0)
    (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s)) :
    IsIso ((smallEtaleDerivedSpecializationStalkAbAt B S hS s t).app
      ((smallEtaleDerivedPushforwardAb f).obj
        ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F)))
```

Spreading out: for a fixed relative dimension,
`AlgebraicGeometry.exists_isPullback_specAdjoin_smoothOfRelativeDimension`
(`StacksFrontier/AlgebraicGeometry/Limits/NoetherianApproximation/ProperSmoothFiniteTypeSubring.lean:109`).

```lean
theorem exists_isPullback_specAdjoin_smoothOfRelativeDimension (R : Type u) [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    ∃ (j : (Finset R)ᵒᵖ) (Y : Scheme.{u}) (h : Y ⟶ (specAdjoinFinsetDiagram R).obj j)
      (q' : X ⟶ Y), IsProper h ∧ SmoothOfRelativeDimension n h ∧
        IsPullback q' f h ((specAdjoinFinsetCone R).π.app j)
```

With `Smooth` only, and no fixed relative dimension,
`AlgebraicGeometry.HodgeSpreadingOut.exists_isPullback_finiteType_properSmooth`
(`StacksFrontier/AlgebraicGeometry/DeRham/HodgeSpreadingOut/FiniteTypeModel.lean:113`,
statements B.10):

```lean
theorem exists_isPullback_finiteType_properSmooth (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] [Smooth f] :
    ∃ (R : Type u) (_ : CommRing R) (φ : R →+* A) (Y : Scheme.{u}) (h : Y ⟶ Spec (.of R))
      (q' : X ⟶ Y), Algebra.FiniteType ℤ R ∧ Function.Injective φ ∧ IsProper h ∧ Smooth h ∧
        IsPullback q' f h (Spec.map (CommRingCat.ofHom φ))
```

Its stage form, `exists_isPullback_affineStageCone_properSmooth`, is the first
step of Stacks' proof of 0GLI over an affine base
(`SmoothProperHigherDirectImageLocallyConstantReduction.lean:474-507`). The same
proof descends the coefficient sheaf to a stage with Tag 0GL2: a locally
constant sheaf of `Λ`-modules of finite type on the limit of a directed system
of quasi-compact, quasi-separated schemes with affine transition maps is the
inverse image of such a sheaf at some stage, and two maps that agree on the
limit agree at a later stage (`smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_moduleCat`,
`Constructible/FiniteLocallyConstantLimit/EssSurj.lean:1143`, with
`Λ : Type (u + 1)` and no Noetherian hypothesis; the forms for `Λ : Type` through
a ring isomorphism at `SmoothProperHigherDirectImageLocallyConstantReduction.lean:116`
and `:136`, used at `:270` and `:283` to descend `F` and the relation
`N • 𝟙 F = 0`). Clause (2) of 0GL2, for finite locally constant abelian
sheaves, is `…_isFiniteLocallyConstant_addCommGrpCat` (`EssSurj.lean:1122`).
These are stated on the small étale sites `SmallEtale.topology B X` of a big
étale site `B`; the 0GLI proof passes to Mathlib's sites with
`SmallEtale.sheafEquiv` (`:265-269`). Statements B.10 give the full text.

Differences from the Library's statements:

- The base `S` is arbitrary: any characteristic, no number field. Neither
  theorem mentions a Galois group, a place or inertia. 0GLI concludes that
  `Rⁱf_*F` is locally constant of finite type on `S_ét`. 0GKD says that the
  specialization map to the stalk at a geometric point of the strict
  henselization is an isomorphism.
- 0GLI takes the coefficients `ModuleCat.{u+1} Λ` with `Λ : Type` Noetherian,
  and `F` locally constant of finite type. 0GKD takes abelian sheaves in
  `Ab.{u+1}` and the specialization map formed in a big étale site `B`. Both
  allow locally constant `F`, which the Harris sheaves `A_r` need, and both
  require torsion prime to the residue characteristics.
- 0GLI and 0GKD need torsion coefficients whose exponent is prime to every
  residue characteristic of the source (`htors`, `hFtors`), and 0GLI also needs
  a Noetherian `Λ : Type`. The premise has any commutative `R : Type u`, and
  places only `v` with `Nat.card M ∉ v` in its conclusion. So both theorems are
  applied with a change of coefficients to `Λ = ZMod e`, `e = Nat.card M`, on
  an open where `e` is invertible (bridge B3).
- `exists_isPullback_finiteType_properSmooth` needs only `Smooth` and
  `IsProper`, as the Library assumes. It gives a model over `Spec R` for a
  finitely generated `ℤ`-algebra `R` embedded in `K`, not over an open of
  `Spec 𝒪_K`. The earlier theorem fixes the relative dimension. The
  Library itself already proves the number-field form: a model over a ring of
  `T`-integers, with smoothness and properness descended to a finite level
  (bridge B3, statements A.5). On that route this Stacks theorem is not needed.
- The general premises have constant coefficients `M`, which the constant
  sheaf on a model extends. For a locally constant coefficient sheaf, such as
  one Harris stage `A_r`, Tag 0GL2 descends the sheaf with its annihilator to a
  stage of any directed limit of the kind above, for instance the models over
  `Spec 𝒪_F[1/N]` with limit `X_U`. Neither Stacks nor the Library assembles
  this. The stage that 0GL2 finds depends on the sheaf, so it does not give one
  open for all `r` at once (bridges B3 and B3′).

### 4.2 Galois smoothness (SGA 4 VII 5.8)

Stacks forms the Galois-equivariant derived global sections in
`Trace/GaloisEquivariantGlobalSections.lean` and
`Trace/GaloisEquivariantDerivedGlobalSections.lean`. The setting is
`(Y : Over (Spec (.of k)))` with `[QuasiCompact Y.hom] [QuasiSeparated Y.hom]`
and `[Algebra.IsSeparable k K]`. The coefficient ring is any `Λ : Type` with
`[Ring Λ]`, and the sheaves are arbitrary objects of `EtaleModules Λ Y.left`:
no torsion or finiteness condition. The identification theorem is stated with
the standard model of the derived category (`HasDerivedCategory.standard`, a
local instance).

- `GaloisModules Λ k K := Stacks.Injectives.ContinuousModule.{0, u, u + 1} Λ (K ≃ₐ[k] K)`
  (`:533`): the `Λ`-modules whose action is continuous for the Krull topology and
  the discrete topology on the module, that is, smooth modules.
- `galoisGlobalSections Λ Y K : EtaleModules.{u, 0} Λ Y.left ⥤ GaloisModules Λ k K`
  (`:546`) sends `F` to `Γ(Y_K, F|_{Y_K})`. The action is
  `fieldBaseChangeGlobalSectionsGaloisAction`, induced by `id_Y × Spec σ`.
  Continuity is `isOpen_stabilizer_fieldBaseChangeGlobalSectionsGaloisAction`
  (`:474`), from 09YQ in degree 0 and the limit cone
  `fieldStageConeIsLimit` (`:220`), which writes `Y_K` as the limit of `Y_E`
  over finite subextensions.
- `galoisDerivedGlobalSections := (galoisGlobalSections Λ Y kbar).rightDerivedFunctorPlus`,
  a functor `D⁺(EtaleModules Λ Y) ⥤ D⁺(GaloisModules Λ k kbar)`
  (`Trace/GaloisEquivariantDerivedGlobalSections.lean:89`). Its cohomology
  objects are discrete Galois modules, so smoothness of the action on each
  `Hⁿ` holds by construction.
- `galoisDerivedGlobalSectionsForgetIso` (`:171`) states that forgetting the
  action gives the restriction to `Y_k̄` followed by `RΓ(Y_k̄, -)`:
  `galoisDerivedGlobalSections Λ Y kbar ⋙ U.mapDerivedCategoryPlus ≅ (restriction).mapDerivedCategoryPlus ⋙ (Γ(Y_k̄, -)).rightDerivedFunctorPlus`.
- `galoisForgetAction_comp_galoisDerivedGlobalSectionsForgetIso`
  (`Trace/GaloisEquivariantCohomologyAction.lean:592`) states that under this
  isomorphism the action of `σ` from the Galois-module structure is
  `galoisRestrictionCohomologyNatTrans Λ Y kbar σ` (`:474`), the action induced
  by `id_Y × Spec σ`.
- Also: `Stacks.Frobenius.galoisCohomologyAction`
  (`Trace/GaloisEquivariantStalkComparison.lean:469`) and
  `Stacks.Frobenius.higherDirectImageFibreAddEquiv_smul`
  (`Trace/GaloisModuleHigherDirectImageStalk.lean:204`), tag 03Q9, for abelian
  sheaves in `Ab.{u+1}`. Over any field `k`, with `K` algebraically closed and
  separable over `k` and `X` qcqs, these give an equivariant isomorphism
  `(R^jα_*F)_{Spec K} ≅ H^j(X_K, F|)`.

The limit theorem itself, tag 09YQ, is in Stacks in four forms (statements
B.7 and B.9):

- On the small *affine* étale sites: the definition
  `Stacks.EtaleCohomology.QcqsLimitCohomology.etaleCohomologyColimit_isColimit`
  (`Colimits/QcqsEtaleCohomologyColimit.lean:233`). Its documentation says that
  it is not compared with mainstream étale cohomology (Stacks 04HR is not done).
- On Mathlib's full small étale sites, in every degree:
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_isLimit`
  (`@[stacks 09YQ]`, `Colimits/SmallEtaleColimitUnconditional.lean:132`). Its
  hypotheses are a nonempty directed index `I : Type v`, a system
  `D : Iᵒᵖ ⥤ Scheme.{max u v}` with affine transition maps and quasi-compact,
  quasi-separated levels, and a limit cone `c`. A big étale site `B` must
  contain every level and the limit. This is a device for fixing the size, and
  `BigEtaleSite.exists_contains_of_small`
  (`StacksFrontier/AlgebraicGeometry/Topologies/Etale/Existence.lean:202`)
  produces one for any small family. The coefficients are a presented system
  `E : PresentedSystem IsColimitPresentation`
  (`Colimits/SmallEtaleCohomologyColimit.lean:343`). It consists of abelian
  sheaves `F_i` on the levels with transition maps (Stacks 0EZL), an abelian
  sheaf `𝒢` on the limit, and legs `f_i^{-1}F_i ⟶ 𝒢` that present `𝒢` as the
  colimit. It also carries, as fields, the cocycle law and the cocone law for
  the induced maps on cohomology. The conclusion `IsCohomologyColimit E p`
  (`:392`), for every `p : ℕ`, is the elementwise colimit statement on
  `Sheaf.H` with coefficients in `AddCommGrpCat.{max u v + 1}`: every class on
  the limit comes from a level, and a class dying on the limit dies at a later
  level. `isColimit_stableCohomologyCocone`
  (`Colimits/SmallEtaleCohomologyIsColimit.lean:300`) turns it into an
  `IsColimit` whose vertex is `Hᵖ(X, 𝒢)`. That module is not in the
  nine-root closure of Section 7.1: its closure has 77 modules, 2 of them
  outside (the module itself and `StacksFrontier.RingTheory.SpreadingOut.ColimitSystemUnivLE`).
  The smoothness argument needs only the elementwise form.
- For the inverse images of one sheaf:
  `isCohomologyColimit_pullbackPresentedSystem`
  (`Colimits/PullbackSystemCohomologyColimit.lean:299`). Here all schemes are
  in `Scheme.{u}` with `I : Type u`. The levels and the limit lie over a scheme
  `S` compatibly, `G` is an abelian sheaf on `S_ét` in `AddCommGrpCat.{u + 1}`,
  and the presented system `pullbackPresentedSystem` (`:289`) of the
  `s_i^{-1}G` is built for the user, with both laws. The theorem finds the
  big étale site itself. Its two halves are stated elementwise for
  restriction maps: `exists_restriction_eq_zero_of_isLimit` (`:358`) and
  `exists_eq_etaleCohomologyMapTo_of_isLimit` (`:373`). The closure of this
  module has 2,370 modules, of which only the module itself lies outside the
  nine-root closure of Section 7.1.
- For the base change to an algebraic extension (Stacks 03Q6):
  `Stacks.EtaleCohomology.exists_finiteDimensional_eq_etaleCohomologyMapTo_of_isAlgebraic`
  and `…exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic`
  (`Colimits/AlgebraicExtensionCohomologyColimit.lean:131`, `:110`). For
  fields `L`, `Ω : Type u` with `Ω/L` algebraic, no separability assumed, a
  quasi-compact, quasi-separated `Y : Scheme.{u}` with `f : Y ⟶ Spec L`, an
  abelian sheaf `G` on `Y_ét` in `AddCommGrpCat.{u + 1}` and every `p : ℕ`:
  every class `y` in `Hᵖ` of the inverse image of `G` on
  `Y_Ω = Spec Ω ×_{Spec L} Y` is the image of a class on some `Y_E`, `E` a
  finite subextension, under `etaleCohomologyMapTo` along the projection
  `Y_Ω ⟶ Y_E` (after the canonical identification of the inverse images); and
  a class on `Y` that dies on `Y_Ω` dies on some `Y_E`. The cone is
  `AlgebraicGeometry.fextPullbackCone`, a limit by `fextPullbackConeIsLimit`
  (`StacksFrontier/AlgebraicGeometry/Variety/Geometrically/QuasiCompactOpen.lean:346`),
  which also assumes only algebraicity. The module applies the pullback form
  above. Its closure has 2,372 modules; two of them lie outside the nine-root
  closure: the module itself and `PullbackSystemCohomologyColimit`.

The smoothness route above uses `galoisDerivedGlobalSections`, whose action is
already the geometric one, and needs `K/k` separable. The algebraic-extension
form gives a second route through the Library's own action, as for FAG
(route (i) of F3), for any algebraic `L/K`. Take `Y = X`, `Ω = L` and for `G` the
abelian sheaf underlying the Library's coefficients on `X`, lifted to
`AddCommGrpCat.{u + 1}`. A class `y ∈ Hⁿ(X_L, -)` is then the image of a class
on some `X_E`, `E/K` finite, and every `σ ∈ Aut(L/E)` fixes it, because
`𝟙 × Spec σ` commutes with the projection `X_L ⟶ X_E`. So the stabilizer of
`y` contains `Aut(L/E)`, which is open. Turning this into the Library's
statement needs a comparison between the Library's `Hⁿ` and Stacks' `Sheaf.H`
of the lifted abelian sheaf, compatible with inverse images (bridge B1), and
the identification of the Library's operator with Stacks' maps
`etaleCohomologyMapTo` on `Sheaf.H` along `𝟙 × Spec σ` (bridge B2). The
composition rule for these maps is already in Stacks
(`Stacks.EtaleCohomology.etaleCohomologyMapTo_comp`, statements B.12).

*The level-colimit statements* (Section 2.4). After the Library's reduction to
one level, take `k = F`, `kbar = F̄`, `Y = X_U` over `Spec F` (quasi-compact and
quasi-separated, being proper), `Λ = R`, and for the sheaf the inverse image of
`M` along `X_U → Spec F`, lifted to Stacks' universe. Each class of
`Hᵈ(Y_F̄, -)` is then fixed by an open subgroup, because `galoisDerivedGlobalSections`
lands in discrete modules and its action is the geometric one. Two
identifications remain on the Library side: the restriction of that sheaf to
`Y_F̄ = X̄_U` with `p_U^* M`, which is a composition of inverse images; and the
Library's operator `g_σ^♯` (`projectionCohomologyMap` along
`EtaleGaloisAction.baseChangeMap _ σ`) with `galoisRestrictionCohomologyNatTrans`
on `Hᵈ` (bridge B2). Both are needed for every `R`, without torsion. The
limit route applies with the same choices, `Ω = F̄` and `G` the lifted inverse
image of `M`; then `g_σ^♯` is compared with Stacks' map on `Sheaf.H` along
`𝟙 × Spec σ` instead.

Differences from the Library's statements:

- The derived-sections route requires `K/k` separable. The Library allows any
  algebraic `L/K`, and so does the algebraic-extension form of 09YQ. For
  number fields, and for `F̄/F` in the Harris statements, the extension is
  separable in any case.
- The Library's action, `constantCohomologyRep` and its Harris analogue, is
  built from one chosen injective resolution and a translation action. The
  Stacks action lives on a derived functor into discrete modules. Both are
  induced by `id × Spec σ`, but the identification remains to be proved
  (bridge B2). For the level-colimit statements, the Library's action is
  instead the operator `g_σ^♯` of Section 2.4, on coefficients pulled back from
  `Spec F`.
- The coefficients are in `ModuleCat.{u+1} Λ` with `Λ : Type` on the
  derived-sections route, and are abelian sheaves in `AddCommGrpCat.{u + 1}` on
  the limit route (bridge B1).

### 4.3 Finiteness (SGA 4 XIV 1.2)

`Stacks.EtaleCohomology.module_finite_compactlySupportedCohomologyGroup_of_isConstructible`,
tag `0GLH` (`DerivedLowerShriek/CompactSupportFinitenessAlgClosed.lean:54`):

```lean
theorem module_finite_compactlySupportedCohomologyGroup_of_isConstructible
    {k : Type u} [Field k] [IsAlgClosed k] (B : BigEtaleSite.{u}) (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] :
    (∀ K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X.obj),
      (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.Plus.homologyFunctor _ q).obj K) ∧
        IsTorsionEtaleModule Λ X.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) →
      ∀ i : ℤ, Module.Finite Λ ((compactlySupportedCohomologyGroup.{u, 0} k f j Λ i).obj K)) ∧
    ((∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) →
      ∀ K : DerivedCategory (EtaleModules.{u, 0} Λ X.obj),
        (∀ q : ℤ, IsBigSiteConstructibleEtaleModule B X Λ
          ((DerivedCategory.homologyFunctor _ q).obj K)) →
        ∀ i : ℤ, Module.Finite Λ
          ((compactlySupportedCohomologyGroupUnbounded.{u, 0} k f j Λ i).obj K))
```

Differences from the Library's statements:

- The theorem is about compactly supported cohomology through a
  compactification `j`. For proper `X̄_U`, Stacks already identifies this group
  with ordinary cohomology (statements B.8). `CompactificationOf.ofProper`
  (`Trace/ProperCohomologyExtComparison.lean:42`) makes a proper scheme its own
  compactification, with the identity as the open immersion.
  `etaleModuleExtensionByZeroIdIso` (`:55`) identifies extension by zero along
  the identity with the identity functor. For any field `k` and `f`
  locally of finite type, quasi-compact and separated, with no bound on the
  dimension, `compactlySupportedCohomologyGroupSingleIso`
  (`TorsionModules/CompactSupportCurveFiniteness.lean:134`) identifies the
  group of 0GLH, `compactlySupportedCohomologyGroup k f j Λ n`, on a sheaf `F`
  placed in degree 0, with `Rⁿ Γ(X̄, j_!F)`. Here `n : ℕ`, while 0GLH is stated
  for `i : ℤ`. Composing the two, with `j = CompactificationOf.ofProper f`,
  gives `Rⁿ Γ(X, F)`. Stacks itself composes `ofProper` and
  `etaleModuleExtensionByZeroIdIso` in this way, for a different group
  functor (`Trace/CurveTopCohomologyConstant.lean:57-63`). It applies
  `compactlySupportedCohomologyGroupSingleIso` in
  `TorsionModules/CompactSupportFiniteness.lean:114`. Both modules lie in the
  nine-root closure of Section 7.1. So for `X̄_U` the conclusion of 0GLH is
  finiteness of Stacks' ordinary cohomology, in Stacks' coefficient category.
- The conclusion is `Module.Finite Λ`, while the Library asks for `Finite` of
  the module. Take `Λ = Rcoeff/m^r Rcoeff`, a finite ring, or `ℤ/m^r`; then a
  finitely generated module is finite.
- The theorem needs the constructibility of `B_r` in Stacks' big-site sense,
  `IsBigSiteConstructibleEtaleModule`. The Library has trivializations of `B_r`
  (`cmHarrisCoefficientSystemTrivialization`), from which locally constant of
  finite type, and so constructible, would follow.

The general premises do not include finiteness, so 0GLH serves only
`HarrisCMCohomologyFiniteStatement`.

### 4.4 What remains to be proved on the Stacks route (bridges)

- **B1, coefficient universe.** The Library's `ModuleCat.{u} R` against Stacks'
  `ModuleCat.{max (u+1) 0} Λ` with `Λ : Type` on the derived-sections route.
  This means an isomorphism of `EtaleDerivedSections.cohomology` with the
  derived functors of Stacks, applied to the universe-lifted sheaf, natural in
  the sheaf and compatible with pullbacks. On the limit route (Section 4.2) the
  target is instead `Sheaf.H` of the underlying abelian sheaf in
  `AddCommGrpCat.{u + 1}`, and there Stacks supplies the change of universe
  (statements B.11): `AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`
  (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleCoefficientLift.lean:176`)
  identifies, on Mathlib's small étale site of `X : Scheme.{u}`, the
  `Sheaf.H` of an abelian sheaf in `AddCommGrpCat.{u}` with that of its lift to
  `AddCommGrpCat.{u + 1}`, in every degree. It is the case of
  `Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/CoefficientUniverseLift.lean:281`),
  the map induced on `Ext` by the lift; Stacks applies it to `𝐆_a` in
  `ArtinSchreierSequence/StructureSheafComparison.lean:295`. Stacks also shows
  that the lift preserves injective objects on the small étale site and
  commutes with higher direct images along a continuous functor of sites
  (`StacksFrontier/CategoryTheory/Sites/UniverseLiftDerived.lean:193`, `:129`).
  What the limit route still needs: (a) the Library's
  `EtaleDerivedSections.cohomology X R n`, derived sections of sheaves of
  `R`-modules in `ModuleCat.{u} R`, against `Sheaf.H` of the underlying abelian
  sheaf in `AddCommGrpCat.{u}`. Stacks proves the module-against-abelian
  comparison (Stacks 03FD, `ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying`,
  `StacksFrontier/CategoryTheory/Sites/GlobalSections/ModuleCohomologyComparison.lean:1089`)
  for sheaves of modules over a sheaf of rings on a small category, as an
  existence statement; we did not check whether it transfers to Mathlib's
  small étale site and the Library's `Sheaf J (ModuleCat R)`. FAG's analogue
  (`forgetRightDerivedSectionsIso`, Section 5.2) is in its own universe. The
  abelian derived sections must then be compared with `Sheaf.H`; Stacks has
  this over each object `T` of an essentially small site, for its `Sheaf.H'`
  (`sheafCohomologyIsoRightDerivedSectionsOfEssentiallySmall`,
  `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedSections/RightDerivedSectionsEssentiallySmall.lean:282`),
  whose use for the Library's `Sheaf.Γ` we did not check. (b) Naturality of
  these isomorphisms and of the universe lift for inverse images: Stacks'
  theorem concerns the inverse images of the lifted sheaf, so the lift must
  commute with inverse image along the projections `X_L ⟶ X_E`, `X_L ⟶ X` and
  `𝟙 × Spec σ`, and the comparisons must carry the Library's pullback maps
  (`cohomologyPullbackWithCoefficients`, `projectionCohomologyMap`) to Stacks'
  `etaleCohomologyMapTo`. `SmallEtaleModuleUniverseComparison.lean` lifts the
  derived internal Hom (08JP), not cohomology.
- **B2, the Galois actions.** The Library's `constantCohomologyRep`,
  `cmHarrisGeometricGaloisCohomologyAction` for Harris, and the level operator
  `g_σ^♯` of Section 2.4, against the action induced by `id × Spec σ` on `Hⁿ`
  of `galoisDerivedGlobalSections`. On the Stacks side,
  `galoisForgetAction_comp_galoisDerivedGlobalSectionsForgetIso` already
  identifies its action with the geometric one. On the limit route the
  Library's operator is compared instead with Stacks' maps
  `etaleCohomologyMapTo` on `Sheaf.H` along `𝟙 × Spec σ`. The fixed-point
  argument uses their composition with the projection `X_L ⟶ X_E`. Stacks
  states this composition rule for successive morphisms with their
  coefficient maps: `Stacks.EtaleCohomology.etaleCohomologyMapTo_comp`
  (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtalePresentedSystem.lean:120`,
  in the nine-root closure; statements B.12). What remains is the comparison
  of the Library's operators with these maps, under B1. The stabilizer bound
  then follows: a class from `X_E` is fixed by `Aut(L/E)`, an open subgroup.
- **B3, spreading out, and the coefficients and base for specialization.**
  This bridge is shared with the FAG route (F4).
  - *The model is an assembly of Library results.* No external theorem is
    needed for it. In the Library at `f050c0b1` (statements A.5; all files
    except `NumberFieldAlmostAllLocalPoints.lean` are unchanged since `fcb85a7e`):
    `Langlands.Global.numberFieldSpreadSeparatedExistence`
    (`Langlands/Global/AdelicSpreadSeparatedExistenceProof.lean:66`) applies
    to `Over.mk f`, which is locally of finite type, quasi-compact and
    separated, and to any finite set of finite places. It gives a larger
    finite set `T` and a model `𝒳` (called `M` in the Lean statement) over
    `Spec` of the ring `(T : Set (FinitePlace K)).integer K` of `T`-integers,
    locally of finite type, quasi-compact and separated, with
    `numberFieldModelGenericFiber K T 𝒳 ≅ Over.mk f`. `numberFieldSpreadEventualSmoothness`
    and `numberFieldSpreadEventualProperness`
    (`AdelicSpreadEventualSmoothFiberGeometryProof.lean:104`,
    `AdelicSpreadEventualPropernessProof.lean:86`) say that a morphism of such
    models is smooth (proper) on the generic fibre exactly when it is so after
    base change to some finite superlevel. Apply both to the structure
    morphism of `𝒳`, seen as a morphism to the terminal object `Over.mk (𝟙 _)`
    of the slice; its generic fibre is `f` up to isomorphism. Base-change
    `𝒳` to the union of the two levels (`numberFieldLevelModelBaseChange`,
    `AdelicLevelModelTransition.lean:114`); smoothness and properness are
    stable under base change. If a principal level is wanted,
    `numberFieldPrincipalLevelAbove` (`NumberFieldPrincipalSIntegerFiniteType.lean:111`)
    enlarges any finite set to the set of places containing one nonzero
    integer `t`, whose ring is `𝒪_K[1/t]` (`numberFieldPrincipalSIntegerEquiv`,
    `:39`) and of finite type over `ℤ` (`:119`). The current Library carries
    out exactly this assembly for `Smooth ⊓ GeometricallyConnected`:
    `Langlands.Global.exists_numberFieldSmoothConnectedModel`
    (`Langlands/Global/NumberFieldAlmostAllLocalPoints.lean:42`), with the
    passage from the structure morphism to the slice in the private lemma
    `property_pullback_structureMap_iff` (`:24`), which a reuse must restate or
    make public. A smooth proper model of `X` is the same assembly with
    `IsProper` in place of geometric connectedness. The finite set `T` depends
    only on `f`. Stacks' `exists_isPullback_finiteType_properSmooth`
    (Section 4.1) is then optional.
  - *Coefficients and base for one finite module `M`.* 0GLI needs a Noetherian
    `Λ : Type` and, like 0GKD, torsion prime to the residue characteristics;
    the premise has any commutative `R : Type u`. Let `e = Nat.card M`. Then
    `e • M = 0`, since the order of an element of a finite group divides
    the group's order, so `M` is a module over `ZMod e`. That ring is Noetherian
    and lies in `Type`, so it is the coefficient ring for 0GLI. The Library's
    cohomology of the constant sheaf `M` of `R`-modules must then be identified
    with the cohomology of `M` as a sheaf of `ZMod e`-modules on Stacks' side
    (or of the underlying abelian sheaf for 0GKD), naturally and compatibly
    with the pullback maps that define the Galois action. Both compute the
    cohomology of the underlying abelian sheaf (the argument of
    `EtaleGaloisGoodReduction/Statement.md`, step 2), so this is part of B1.
    For the base, let `v ∉ T` with `e ∉ v`. Base-change the model to the level
    `T ∪ numberFieldPrincipalExceptional K e`, whose places are those of `T`
    and those whose prime contains `e` (`mem_numberFieldPrincipalExceptional`,
    `NumberFieldPrincipalSIntegerFiniteType.lean:26`). On that ring `e` is a
    unit: it is a unit in the ring of the level `numberFieldPrincipalExceptional K e`,
    which `numberFieldPrincipalSIntegerEquiv` identifies with the localization
    `𝒪_K[1/e]`, and that ring maps into the larger one by `numberFieldSIntegersMap`.
    The Library does not state this consequence. `v` is not in that level,
    because `e ∉ v`. So the residue characteristics of
    the new base do not divide `e`, and `htors` holds with `n = e`.
    Alternatively, work at the strict henselization at `v`, where `e` is a
    unit. Either way the set `S = T` of the premise is chosen from the model
    alone, before `M`, as the premise's order of quantifiers requires; only
    the open on which the specialization theorem is applied depends on `M`.
  - *The Harris stages.* The stalk module of `A_r` is a finite `Rcoeff`-module
    of `p`-power order (step 1 of the argument in
    `HarrisCMCohomologyUnramified/Statement.md`), so `A_r` is killed by a
    power `p^{a_r}`. Take `Λ_r = ZMod (p^{a_r})` (Noetherian, in `Type`) for
    0GLI. The Library's exponent `m^r` (Section 2.2) need not be prime to the
    residue characteristics and is not the one to use. On the single open
    `T' = Spec 𝒪_F[1/pN]` of B3′, `p` is a unit, hence so is every `p^{a_r}`.
    So one open serves every stage.
  - *Locally constant coefficients.* For a locally constant coefficient
    sheaf, Tag 0GL2 descends it to a stage of the system of models (Section
    4.1), after the passage from the Library's coefficients to
    `ModuleCat.{u+1} Λ` (B1) and from Stacks' `SmallEtale.topology B` to
    Mathlib's site. For Harris this is not enough: `HarrisCMCohomologyUnramifiedStatement`
    fixes one finite set `S` before quantifying over every stage `r`, so one
    arithmetic open must carry, for every `r` at once, a locally constant
    extension of `A_r`. Descending each `A_r` separately with 0GL2 gives an
    open that depends on `r`. The uniform extension is a separate obligation
    (bridge B3′ below). The model of `X_U` itself is the Library assembly
    above.
- **B3′, uniform extension of the Harris coefficients.** One open
  `T' = Spec 𝒪_F[1/pN]`, a smooth proper model `𝒳'` of `X_U` over it, and
  locally constant constructible sheaves `𝒜_r` on `𝒳'` extending every `A_r`.
  The Library's own documentation of `HarrisCMCohomologyUnramifiedStatement`
  (`Langlands/Cohomology/HarrisCMCohomologyUnramified/Statement.md`, section
  "Why the statement is expected to hold", steps 1–5) gives the route: a model
  of each component with an abelian scheme extending the universal one, chosen
  once (Stacks 01ZM); control of the monodromy of every coefficient
  cover by the `p`-power torsion of that abelian scheme; and descent of every
  `A_r` along `π_1(X_c) → π_1(𝒳'_c)` (SGA 1 V 8.2). Neither library contains
  this argument; Stacks' spreading-out theorem and 0GL2 cover its single-sheaf
  steps only. 0GLI and 0GKD apply only after `𝒜_r` is given.
- **B4, from locally constant to unramified.** From 0GLI or 0GKD, applied
  with `Λ = ZMod e` on the base of B3 where `e` is invertible, to
  `DecompositionGroupAction.IsUnramifiedAt`. This needs the
  stalk at a geometric point over `v` against the generic stalk, the absolute
  Galois group of the fraction field of the strict henselization against the
  inertia subgroup of the completion `K_v` (with Mathlib's chosen embedding),
  and the compatibility of the actions. Stacks has
  `AlgebraicGeometry.continuousSMul_etaleStalkGal`
  (`GaloisActionStalks/SchemeStalkAction.lean:491`) for a stalk action that is
  defined differently from `Stacks.Frobenius.fieldGaloisStalkAction`
  (`Trace/GaloisEquivariantStalkComparison.lean:116`), the action used by 03Q9.
  Stacks does not link the two. For the second identification Stacks has the
  ring theory in global form, for a normal local domain `A` with a separable
  closure `L` of its fraction field `K` and a prime `q` of the integral
  closure `B` over the maximal ideal: a strict henselization of `A` is
  `A`-isomorphic to the inertia invariants `(B_q)^I`, and its fraction field
  embeds into `L` with image the inertia field `L^I`
  (`IsIntegralClosure.nonempty_algEquiv_inertiaInvariants_of_indEtale`,
  `…exists_ringHom_fractionRing_range_eq_inertiaFixedField`,
  `StacksFrontier/RingTheory/Invariant/StrictHenselizationInertiaEmbedding.lean:72`,
  `:91`); likewise `K^h = L^D` for the decomposition group
  (`DecompositionFixedField.lean`). The passage from these global groups to the
  inertia subgroup of the completion was not looked for. FAG's corresponding
  results are in F5.
- **B5, finiteness.** Stacks already identifies compactly supported with
  ordinary cohomology for proper `X̄_U` (Section 4.3). What remains is the
  passage from Stacks' cohomology to the Library's (B1) with the change of
  coefficient ring to `Λ = Rcoeff/m^r Rcoeff`, the change of degree index from
  `ℤ` to `ℕ`, big-site constructibility of `B_r`, and the step from
  `Module.Finite` over a finite ring to `Finite`.
- **B6, separability.** Only on the derived-sections route:
  `galoisDerivedGlobalSections` needs `K/k` separable, while
  `GaloisCohomologySmoothStatement` allows any algebraic `L/K`. The limit route
  covers inseparable `L/K`, since the algebraic-extension form of 09YQ assumes
  only algebraicity. On the cohomological route all fields have
  characteristic 0, so the case does not arise there.

Stacks itself proves no other input that these premises need. Generic base
change is not in Stacks: `StacksFrontier/EgaSgaIndex/SGA4Half.lean` lists only Th. finitude
2.1, 2.7 and 3.1 (special cases) and 5.2.4 (partial, through 0GKD).

## 5. The FAG repository (formal-arithmetic-geometry/weil-conjectures, a25955c)

### 5.1 Pin, licence, reading copy

Commit `a25955cde4f85f67bef3149a6efc3efe20c22132`, registered as literature
`formal-arithmetic-geometry-weil-conjectures-a25955c`. Apache-2.0
(`LICENSE` at the root). `lean-toolchain` Lean 4.35.0; `lakefile.toml` requires Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and sets `warn.sorry = false`,
`backward.isDefEq.respectTransparency = false`, `maxSynthPendingDepth = 3`. 26,800 Lean files:
the library `WeilConjectures` (with the subdirectories `WeilConjectures/Mathlib`, 765 files of
material written for Mathlib, and `WeilConjectures/FromJoel`, 81 files migrated from a Mathlib
fork) and the Comparator libraries `Weil.*`, `LeanEvalWeil.*` under `Comparator/`. Every file
uses the module system (`module`, `public import`, `@[expose] public section`). The README says
that the main theorems are proved without `sorry` and that `#print axioms` at commit `91ebbc09a7`
showed only the three standard axioms; that was not rechecked here.

### 5.2 Conventions of its étale layer

The torsion étale theory (`WeilConjectures/SixFunctors/Etale`, `ConstructibleSheaf`,
`AlgebraicGeometry/Sites`) works on Mathlib's small étale site, as the Library does. Coefficients
are sheaves `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` with `X : Scheme.{u}` and
`Λ : Type (u + 1)` a commutative ring; `R((f)_*[…])`, `R+(…)` are the derived direct images on
`D` and `D⁺`, built from Mathlib's derived categories. Cohomology appears in three forms:
homology of the derived global sections, `Ext (constSheaf Λ) F q`, and Mathlib's `Sheaf.H` of
an abelian sheaf. FAG has three comparisons between them, each on a quasi-compact,
quasi-separated scheme (statements C.11):

- `AlgebraicGeometry.Etale.bijective_mapExtComp_constantIntToRing`
  (`SixFunctors/Etale/ConstantCohomologyExt.lean:68`): for every sheaf `Y` of `Λ`-modules and
  every `n`, the map `Extⁿ(Λ_X, Y) ⟶ Hⁿ(X_ét, Y)` to `Sheaf.H` of the underlying abelian sheaf,
  given by composition with the class `ℤ_X ⟶ Λ_X` of `1`, is bijective.
- `unitShiftAddEquivH` (`:90`): the special case of the unit, `Hom(Λ_X, Λ_X[n])` in the
  derived category against `Hⁿ(X_ét, Λ)` of the underlying abelian sheaf of `Λ_X`.
- `forgetRightDerivedSectionsIso` (`SixFunctors/Etale/ForgetModuleCohomology.lean:102`): for
  every sheaf `G` of `Λ`-modules and every `q`, the derived global sections `Rᵠ Γ(X_ét, G)`,
  computed in sheaves of `Λ`-modules, are as an abelian group those of the underlying abelian
  sheaf.

All three stay in FAG's coefficient universe (`ModuleCat.{u + 1} Λ` and
`AddCommGrpCat.{u + 1}`), and none involves a Galois action.

The Library's cohomology is `(Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u} R)).rightDerived n`
with `R : Type u`. So the site agrees, and the coefficient category differs in two universes:
the module universe (`u` against `u + 1`) and the ring universe (`R : Type u` against
`Λ : Type (u + 1)`, so that `Λ = ULift R` at best). The Stacks repository has the first
difference only (its `Λ : Type`).

The pro-étale layer with condensed coefficients (`SixFunctors/ProEtale`, `WeilSheaf`) is not
needed for any premise of the cohomological branch, although not every premise is a torsion
statement. The good-reduction and unramified premises concern finite modules `M` or the stages
`B_r`, on which `m^r` acts as zero, and so do the Harris finiteness and Harris smoothness
premises: all of these are torsion statements. The other smoothness premises are not:
`GaloisCohomologySmoothStatement` quantifies over every `M : ModuleCat R`, and
`HarrisCMLevelGaloisSmoothStatement` and its prime-to-`m` variant over every sheaf of
`R`-modules on `Spec F`, for any ring `R` (Section 2.4). The theorem that serves them, FAG's 09YQ, works on the small étale site and
needs no torsion: its module documentation (`AlgebraicGeometry/Sites/CohomologyLimit.lean`,
lines 13–16) says that no torsion hypothesis is needed, and its statement has none. So the
étale layer suffices for every premise.

### 5.3 Theorems for each premise

Part C of [`statements.md`](etale-premises-sheaf-libraries-evidence/statements.md) gives the
full Lean text of every FAG theorem in this table, with the namespaces and section variables
in scope. The table states only the hypotheses and what differs from the Library.

| Library premise | FAG theorem | What differs from the Library's statement |
|---|---|---|
| `GaloisCohomologyGoodReductionStatement`, `HarrisCMCohomologyUnramifiedStatement` (SGA 4 XVI 2.1–2.2) | `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper` and its strictly local form `…_homology_lowerStar_of_smooth_of_isProper` (`SixFunctors/Etale/BaseChangeTheorems/SmoothProperLocallyConstant.lean:180`, `:153`) | Any base `Y` (mixed characteristic allowed), `f` smooth and proper, `Λ` killed by `N ≠ 0` invertible on `Y`, `F` locally constant (`IsLocallyConstantSheaf`, instance for constant sheaves in `ConstructibleSheaf/DenseOpenUnit.lean:227`); for a geometric point `s` of `Y` and a geometric point `t` of the strict localization, restriction `Γ(Y_(s), g^* Rᵠf_*F) → Γ(Spec Ω', t^* g^* Rᵠf_*F)` is an isomorphism. No Galois group, no number field, no spreading out. The local-constancy form (SGA 4 XVI 2.2), `Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper` (same file, `:226`), needs `Y` of finite type over a field and `Λ` finite, so it does not apply over an open of `Spec 𝒪_K`; the specialization form suffices for unramifiedness. The premise's coefficients `M` over an arbitrary `R` must first be moved to a ring killed by `Nat.card M`, and the base to an open on which that number is a unit (bridge F4). |
| same, auxiliary | proper base change `Etale.isIso_baseChange_of_isProper` (`@[stacks 0DDE]`, `BaseChangeTheorems/Proper.lean:145`) and `Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring` (`:168`); smooth base change `Etale.isIso_baseChange_of_smooth` (`BaseChangeTheorems/Smooth.lean:58`) | Statements on `D⁺` of the FAG coefficient categories, for a pullback square `sq : IsPullback g' f' f g`. Proper base change: `[IsProper f]`, any `g`, and either a complex `K` of abelian sheaves in `Ab.{u+1}` whose cohomology sheaves are torsion (`hK : Etale.DerivedCategory.Plus.torsionHomology X K`), or sheaves of `Λ`-modules with `IsAddTorsion Λ`. Smooth base change: `[QuasiCompact f] [QuasiSeparated f]` (section variables), `[Smooth g]`, and `hK : Etale.DerivedCategory.Plus.orderInvertibleOnHomology f K`: in every cohomology sheaf of `K`, the order of every element of every geometric stalk is a unit on `Y`. |
| `GaloisCohomologySmoothStatement`, `HarrisCMGaloisCohomologySmoothStatement`, `HarrisCMLevelGaloisSmoothStatement`, `HarrisCMPrimeToGaloisSmoothStatement` (SGA 4 VII 5.8) | The limit theorem `AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit` and `…_eq_zero_of_isLimit` (`@[stacks 09YQ]`, `AlgebraicGeometry/Sites/CohomologyLimit.lean:178`, `:271`), and its form for `Sheaf.H`, `Etale.cohomologyMap_isColimit_of_isLimit` (`AlgebraicGeometry/Sites/CohomologyContinuity.lean:115`); the limit cones over finite subextensions (`FiniteIntermediateField.isLimitSpecCone`, `AlgebraicGeometry/IntermediateFieldLimit.lean:257`; `isLimitOverCone`, `SixFunctors/ProEtale/GaloisAcyclic/FieldExtension.lean:91`; `Scheme.Hom.isLimitFiniteLevelCone`, `WeilSheaf/CondensedModelFiniteLevelColimit.lean:363`); the composition rule `Etale.cohomologyPullbackFunctorial` (`AlgebraicGeometry/EtaleCohomologyPullbackFunctorial.lean:35`). The stalk formula `AlgebraicGeometry.Etale.nonempty_geometricStalk_higherDirectImage_addEquiv` (`@[stacks 03Q9]`, `SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/StalkFormula.lean:477`) with its comparison map `higherDirectImageStalkComparison` (`:446`, `:459`); the strict henselization of a field (`AlgebraicGeometry/Sites/StrictHenselizationField.lean:50`, `:66`, `:108`, `:119`) and the factorization of a geometric point through its strict localization (`AlgebraicGeometry/Sites/StrictHenselizationLocal.lean:430`); topological invariance `Etale.cohomologyMap_bijective` (`@[stacks 03SI]`, `SixFunctors/Etale/UpperLowerStar/TopologicalInvariance.lean:223`); the Galois point and discrete modules (`AlgebraicGeometry/Sites/GaloisModule.lean`, `AlgebraicGeometry/EtaleSheafDiscreteContinuousRep.lean:45`, `:56`, `:70`) | Statements C.4, C.6, C.9 and C.10. *09YQ:* a cofiltered system `D : I ⥤ Over S`, `I : Type u` small, of qcqs schemes with affine transition maps and a limit cone; `F` a sheaf on `S`; every class in `Ext(Λ, F\|_X) q` on the limit comes from a stage, and one dying on the limit dies at a stage. The `Sheaf.H` form `cohomologyMap_isColimit_of_isLimit` has the same hypotheses, with the limit condition on the underlying cone of schemes and `F` an abelian sheaf in `AddCommGrpCat.{u + 1}`; its maps are `Etale.cohomologyMap` (statement C.10). *03Q9:* for `f : X ⟶ S` quasi-compact and quasi-separated, a geometric point `s : Spec Ω ⟶ S` with `Ω` separably closed, any sheaf `F` of `Λ`-modules on `X` and any `q`, the stalk of `Rᵠf_*F` at `s` is additively isomorphic to `Ext(Λ, F\|) q` on `S_(s) ×_S X`, where `S_(s)` is the strict localization. The theorem states only that such an isomorphism exists (`Nonempty (… ≃+ …)`). The file defines the map: the germ of a class on `V ×_S X` goes to its restriction along the point `S_(s) ×_S X ⟶ V ×_S X` (`:446`, `:459`), and this restriction is compatible with further pullback (`cohomologyPresheafRestrict_comp'`, `:358`). That this map is bijective is shown only inside the proof (`:492`). There is no torsion and no properness hypothesis. *The field:* for `S = Spec K`, the strict henselization at `Spec Ω ⟶ Spec K` is a field (`:108`) whose evaluation into `Ω` is injective (`:66`) and reaches every element of `Ω` separable over `K` (`:50`). So for a separable closure `Ω` the evaluation is an isomorphism onto `Ω`. For `Ω` algebraic over `K`, `Spec Ω ⟶ Spec K_(s)` is a universal homeomorphism (`:119`), along which FAG's 03SI identifies the cohomology of abelian sheaves (`Sheaf.H` with `AddCommGrpCat` coefficients). For every geometric point `s`, `Spec.map (strictHenselizationEval s) ≫ strictLocalizationToBase s = s` (`spec_map_strictHenselizationEval_comp_strictLocalizationToBase`, `StrictHenselizationLocal.lean:430`). `AlgebraicGeometry/Sites/FieldCohomologicalDimension.lean:114-127` uses this factorization and the universal homeomorphism over a field, for an algebraic closure `Ω`, to carry a bound on cohomological dimension from `pullback a s` (the base change to `Ω`) to `pullback a (strictLocalizationToBase s)`, and from there to the vanishing of higher direct images. *The Galois point:* the Galois point `Scheme.galoisPoint` of `Spec K`; the equivalence `Scheme.etaleSheafEquivDiscreteModule` between abelian étale sheaves on `Spec K` and discrete `Gal(Ω/K)`-modules; `Hⁿ(Spec K, F) ≃ Hⁿ(Gal(Ω/K), F_Ω)` (`sheafHAddEquivGaloisH`) (`GaloisModule.lean:97`, `:128`, `:372`, `:386`, `:400`); and the same equivalence with discrete continuous representations of `Gal(Ks/K)` (`Scheme.etaleSheafEquivDiscreteContinuousRep`). Its underlying group is the stalk at `Spec Ω ⟶ Spec K` (`…ForgetIso`), and `σ` acts on the germ at a lift `x` as the germ at `Spec τ ≫ x`, for any `τ ∈ Aut(Ω/K)` extending `σ` (`…ForgetIso_ρ`). *What FAG lacks:* we found no analogue of the Stacks repository's `galoisDerivedGlobalSections`, that is, no Galois-equivariant `RΓ` and no Galois action on `Hⁿ(X_Ω, F)` for every `n`, where `X_Ω` is a scheme base-changed to a separable closure `Ω`. The search covered the 736 FAG files that mention `Gal(` or `≃ₐ[`, 60 of which also mention the small étale site, `Sheaf.H`, a right derived functor or `Ext`. FAG has the automorphisms `𝟙 × Spec σ` of the geometric fibre `X ×_K Spec K̄` (`Scheme.Hom.geometricFiberGaloisMap`, `AlgebraicGeometry/GeometricFrobenius.lean:341`), which it uses for Picard groups, group laws and `H¹` of curves. Its other Galois actions are on stalks at geometric points, on fibre functors of finite étale covers, on cohomology over finite fields, and on nearby cycles, the last in the pro-étale layer (`SixFunctors/NearbyCycles/GaloisAction.lean`). *Two routes (bridge F3).* (i) Show the Library's own action (`galoisCohomologyRep`, `cmHarrisGeometricGaloisCohomologyAction`) smooth from 09YQ: write `X_L = lim X_E` over the finite subextensions `E` of `L/K`; a class coming from `X_E` is fixed by `Aut(L/E)`. FAG has every geometric input (statements C.10). `FiniteIntermediateField.isLimitSpecCone` writes `Spec L` as the limit of the `Spec E` for any algebraic extension `L/K`. `overCone` and `isLimitOverCone` (`FieldExtension.lean:80`, `:91`) give the same cone in `Over (Spec K)`. A proof in that file (`:155-159`) pulls it back along a scheme over `Spec K` and maps it to the slice over another scheme; it then applies the vanishing form of 09YQ (`:176`). That pulled-back cone exists only inside the proof. For a morphism `f : X₀ ⟶ Spec k`, `Scheme.Hom.isLimitFiniteLevelCone` exports the cone `X₀ ⊗_k k̄ = lim_E X₀ ⊗_k E` for `k̄ = AlgebraicClosure k`, as a diagram of schemes (not of schemes over a base), with affine transition maps, and with quasi-compact, quasi-separated stages when `X₀` is (instances `:336`, `:341`, `:345`). `Etale.cohomologyMap_isColimit_of_isLimit` is 09YQ for `Sheaf.H` along such a cone, and `Etale.cohomologyPullbackFunctorial` is the composition rule for `Etale.cohomologyMap` (with naturality in the sheaf), which the fixed-point argument uses. For the Harris statement the sheaf `B_r = π^* A_r` is pulled back from `S = X_U`, which is the form FAG's statement needs. For the level statements, after the Library's reduction to one level (Section 2.4), take `S = Spec F`, the stages `X_U ×_F Spec E` over the finite subextensions `E` of `F̄/F`, and the sheaf `M` itself: the cohomology on each stage and on `X̄_U` is then that of the inverse image of `M`, as in the Library's statement. A class `y` on `X̄_U` comes from some `X_U ×_F Spec E`, and each `σ ∈ Gal(F̄/E)` fixes it, because the automorphism induced by `σ` commutes with the projection to that stage. Turning this into `g_σ^♯ y = y` needs three things that FAG does not provide: the comparison of the Library's `Hⁿ` with `Sheaf.H` of the lifted abelian sheaf (bridge F1), the identification of `g_σ^♯` with `Etale.cohomologyMap` along `𝟙 × Spec σ` (bridge F2), and the cone in the form the theorem takes, a diagram in `Over S` for the base `S` of the sheaf (lifting the finite-level cone, as the proof in `FieldExtension.lean` does). FAG states the composition rule for `Etale.cohomologyMap` but not for its `Ext` maps `cohomologyRestrictOver`; route (i) therefore runs through `Sheaf.H`. (ii) Go through the Galois point: for the structure morphism `f` of `X` over `Spec K` and the coefficient sheaf `F`, 03Q9, the field lemmas and 03SI, once assembled as listed in F3, identify `Hᵠ(X_Ω, F)` with the stalk of `Rᵠf_*F` at `Spec Ω`. The equivalence with discrete continuous representations makes that stalk a discrete representation, so every element has an open stabilizer. Whether the transported action is the action of `𝟙 × Spec σ` is not proved in FAG (bridge F3). Neither route has a torsion hypothesis, so arbitrary coefficients are covered. |
| `HarrisCMCohomologyFiniteStatement` (SGA 4 XIV 1.2) | `AlgebraicGeometry.Etale.isIso_homology_derivedBaseChangeMapPlus_of_isProper` (`SixFunctors/Etale/Derived/Finiteness/Proper.lean:205`); also `isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper` (`:179`) | `Λ : Type (u+1)` finite, killed by an integer invertible in the field `k`; `f : X ⟶ S` proper, `S` of finite type over `k`, a bound `d` on the dimension of geometric fibres, `F` constructible (`IsConstructibleSheaf`); conclusion includes that `Rᵠa_{s*}(i_s^* F)` on `Spec Ω` is a finite sheaf (`IsFiniteSheaf`: finitely generated stalks), for `Ω` algebraically closed. For `X̄_U → Spec F̄` this gives finiteness of `Hᵠ(X̄_U, B_r)` once `R = HarrisCoefficientIntegers K p` is replaced by the finite ring `R/m^r R` (or `ℤ/m^r`), `B_r` is shown constructible in FAG's sense, and the dimension bound is supplied. The compact-support form `finite_compactlySupportedCohomology` (`Finiteness/CompactSupport.lean:157`) needs finite Tor amplitude and is not the right tool for `B_r`. |
| `GaloisCohomologyUnramifiedStatement` (SGA 4½, Th. finitude 1.9) | Two forms over a base of finite type over a field. **Open immersion:** `AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn` (`SixFunctors/Etale/Derived/Finiteness/Deligne.lean:410`), with the property `HasConstructibleDirectImageBaseChangeOn` (`…/Finiteness/Deligne/Defs.lean:56`); its case `S = Spec k` is `boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field` (`Deligne.lean:446`). **Smooth source:** `AlgebraicGeometry.Etale.smoothGenericDirectImage` (`Deligne.lean:342`), which proves the statement `SmoothGenericDirectImage` (`…/Deligne/Statement.lean:110`) with the property `HasDirectImageBaseChangeOnPlus` (`…/Deligne/Plus.lean:70`); FAG derives it (`Deligne.lean:298`) from the prime-field form `exists_nonempty_open_smooth_directImage_lisse_baseChange` (`AlgebraicGeometry/SmoothGenericDirectImage.lean:123`) | Statements C.5 and C.8. The site is the Library's. Common hypotheses: `Λ : Type (u+1)` finite, with `HasInvertibleExponent Λ S` (some `n > 0` with `n = 0` in `Λ` is a unit on `S`); `S` integral, locally of finite type and quasi-compact over a field `k`. *Open-immersion form:* `fY : Y ⟶ S` locally of finite type and quasi-compact; `j : X ⟶ Y` an open immersion; `F` a constructible sheaf on `X`. Conclusion: a nonempty open `U ⊆ S` such that for every noetherian `T` with a morphism `t : T ⟶ S` whose image lies in `U`, and every base change `j_T : X_T ⟶ Y_T` of `j` along `T ×_S Y ⟶ Y`, the complex `R(j_T)_*(g'^*F)` is bounded constructible and the derived exchange map `Lg^* Rj_*F ⟶ R(j_T)_* Lg'^*F` is an isomorphism. *Smooth-source form:* `a : X ⟶ S` smooth, separated and quasi-compact; `F` a finite locally constant sheaf on `X` (`IsFiniteLocallyConstantSheaf`). Conclusion: the same property with `Y = S`, `fY = 𝟙 S` and `j = a`, for `F` placed in degree 0 of `D⁺`: a nonempty open `U ⊆ S` such that for every noetherian `T` and `t : T ⟶ S` with image in `U`, the complex `R(a_T)_*(g'^*F)` is bounded constructible and the exchange map `t^* Ra_*F ⟶ R(a_T)_* g'^*F` is an isomorphism. For a sheaf in degree 0 the two properties agree (`hasConstructibleDirectImageBaseChangeOn_iff`, `Plus.lean:94`). The smooth-source form applies to morphisms that are not open immersions, for instance the projection of the affine line over `S`; FAG uses it as the smooth step in the proof of the open-immersion form. Its prime-field form has coefficients `ULift (ZMod ℓ)` with `ℓ ≠ char k`, and also states that the cohomology sheaves of the direct image are finite locally constant over `U`. Deligne's theorem (SGA 4½, Th. finitude 1.9, printed p. 236, PDF p. 275; setting on printed p. 233, PDF p. 272) is for a noetherian `S`, schemes `X` and `Y` of finite type over `S`, an `S`-morphism `f : X → Y`, and a constructible sheaf `F` of `A`-modules on `X`, with `A` left-noetherian and killed by an integer invertible on `S`. It gives a dense open `U` of `S` over which the `Rⁱf_*F` are constructible and zero for all but finitely many `i`, and their formation commutes with every base change `S' → U`. For `S` the spectrum of a field, `U = S`. FAG's forms replace `f` by an open immersion, or by a smooth, separated, quasi-compact source with finite locally constant coefficients. They allow base changes from noetherian `T` only, and need a field below `S`. The premise's coefficients are a finite `R`-module `M` with `R : Type u`, and its classical proof applies the theorem to a model of `X` over an open of `Spec 𝒪_K`. Such an open has mixed characteristic and is not a scheme over a field, so neither form applies to it. Over `S = Spec K` the only nonempty open is `Spec K` itself. There both forms give bounded constructibility of the direct image and its base change to every noetherian `K`-scheme, and nothing about places. So FAG does not give this premise. `TraceFormula/GenericBaseChange.lean` is a different statement: base change along a product projection `X × U → X × Y` over a field (blueprint lemma, `ℚ̄_ℓ` coefficients). |

The registered
FAG copy was searched for every file that mentions `galoisPoint`, `etaleSheafEquivDiscreteModule` or
`etaleSheafEquivDiscreteContinuousRep`. There are twelve such files, and all concern sheaves
on the spectrum of a field: Galois cohomology of fields, cohomological dimension, the units
sheaf, the comparison with larger geometric points, and stalks over function fields of
curves. The checkout was searched for every file that
mentions `HasConstructibleDirectImageBaseChangeOn`, `HasDirectImageBaseChangeOnPlus` or
`SmoothGenericDirectImage` (either capitalization). These are `Deligne.lean`, the 19
modules of its proof under `Derived/Finiteness/Deligne/`, the root module (which imports
`AlgebraicGeometry.SmoothGenericDirectImage`), and one module documentation in the
pro-étale layer (`ProEtale/FiniteCoefficient/Derived/BoundedHom.lean`). The open-immersion
form has one application, the generic-fibre comparison `Derived/GenericFibre/DirectImage.lean`,
also over a field base. The stalk formula is used in one other file,
`AlgebraicGeometry/StrictLocalHigherImageVanishing.lean`, to detect the vanishing of higher
direct images.

### 5.4 What remains to be proved by us on the FAG route (bridges)

- **F1, coefficients.** An isomorphism, natural in the sheaf and compatible with pullbacks, between the Library's `EtaleDerivedSections.cohomology X R n` (on `ModuleCat.{u} R`) and FAG's cohomology of the lifted sheaf on `ModuleCat.{u+1} (ULift R)`, for both `Hⁿ` forms FAG uses (`Ext(Λ, -)` and homology of derived sections); and a change of coefficient ring, from `R` to a finite quotient for the finiteness theorem and to a ring killed by `e = Nat.card M` for specialization (F4). The lift `ULift R` alone does not serve specialization: it has the characteristic of `R`, so for `R = ℤ` no `N ≠ 0` satisfies FAG's hypothesis `(N : Λ) = 0`. Route (i) of F3 needs the comparison with `Sheaf.H` of the underlying abelian sheaf in `AddCommGrpCat.{u + 1}` instead. Inside FAG's universe, the three comparisons of Section 5.2 relate its two module forms to `Sheaf.H` and to derived sections of the underlying abelian sheaf. None of them changes the universe or the ring, so what remains is the step from `ModuleCat.{u} R` to FAG's categories.
- **F2, the Galois actions.** The Library's operator `cohomologyPullbackWithCoefficients g_σ …`, and for the level statements the operator `g_σ^♯` of Section 2.4 (`projectionCohomologyMap` along `EtaleGaloisAction.baseChangeMap _ σ`), against FAG's pullback maps. On route (i) of F3 these are `Etale.cohomologyMap` on `Sheaf.H`, whose composition rule FAG states (`Etale.cohomologyPullbackFunctorial`). FAG's `Ext` forms `cohomologyRestrict`/`cohomologyRestrictOver` have no stated composition rule, so a comparison made with them would also need that rule.
- **F3, smoothness.** One of the two routes of the smoothness row of Section 5.3.
  - (i) *The limit.* FAG supplies the limit cone over the finite subextensions of an algebraic extension, 09YQ for `Sheaf.H` (`Etale.cohomologyMap_isColimit_of_isLimit`) and the composition rule for `Etale.cohomologyMap` (`Etale.cohomologyPullbackFunctorial`) (Section 5.3, statements C.10). Still to be done: F1 with `Sheaf.H` as target; F2 with `Etale.cohomologyMap` along `𝟙 × Spec σ` as FAG's map; and the cone as a diagram over the base of the sheaf. `isLimitFiniteLevelCone` is a diagram of schemes, and the lift of the cone of `Spec L` to a slice is done only inside a proof (`FieldExtension.lean:155-159`). The fixed-point argument itself is then short.
  - (ii) *The Galois point.* Its scope is narrower than route (i). FAG's equivalence `Scheme.etaleSheafEquivDiscreteContinuousRep` (`AlgebraicGeometry/EtaleSheafDiscreteContinuousRep.lean:45`, statements C.9) is for `Gal(Ks/K)` with `Ks` a separable closure of `K` (`[IsSepClosed Ks] [Algebra.IsSeparable K Ks]`, `:39-40`). Its comparison with the stalk at `Spec Ω ⟶ Spec K` (`…ForgetIso`, `…ForgetIso_ρ`, `:56`, `:70`; variables at `:51-52`) is for a separably closed `Ω` over `Ks`. So the route gives smoothness on `Hᵠ(X_Ks, F)`. For the Library's `L = AlgebraicClosure K` it also needs the transport along the restriction isomorphism `Aut(K̄/K) ≅ Gal(Ks/K)`, with 03SI along the universal homeomorphism `X_K̄ ⟶ X_Ks`. It does not reach an algebraic extension `L/K`, separable or not, whose field is not separably closed, because `Spec L ⟶ Spec K` is then not a geometric point. `GaloisCohomologySmoothStatement` quantifies over every algebraic `L/K`, so in general it needs route (i).
    FAG supplies the stalk comparison (03Q9), the strict henselization of a field, the factorization of a geometric point through its strict localization, topological invariance (03SI), the comparison of `Ext(Λ, -)` with `Sheaf.H`, and the discrete representation on the stalk of a sheaf on `Spec K`. Still to be done: (a) the field case of the stalk formula. There `S_(s) = Spec K_(s)` (FAG defines the strict localization as the spectrum of the strict henselization), and `s` factors as the evaluation `u : Spec Ω ⟶ Spec K_(s)` followed by `strictLocalizationToBase s` (`StrictHenselizationLocal.lean:430`). `FieldCohomologicalDimension.lean:114-127` builds from this factorization the induced map `pullback f s ⟶ pullback f (strictLocalizationToBase s)` (an isomorphism for a separable closure, a universal homeomorphism for an algebraic closure), but uses it only to carry a bound on cohomological dimension. What remains is to apply 03SI along that map to identify the cohomology of `pullback (strictLocalizationToBase s) f` with that of `X_Ω`; (b) a lemma stating that the explicit comparison map `higherDirectImageStalkComparison` is bijective, since the theorem exports only the existence of an isomorphism and the bijectivity is proved inside its proof (`StalkFormula.lean:492`); (c) the passage between `Ext(Λ, -)` of sheaves of `Λ`-modules, used by 03Q9, and `Sheaf.H` of abelian sheaves, used by 03SI. This is FAG's `bijective_mapExtComp_constantIntToRing` (Section 5.2), for every sheaf of modules; its compatibility with the pullback maps is part of (d); (d) equivariance: under these identifications `σ` acts on `Hᵠ(X_Ω, F)` as the pullback along `𝟙 × Spec τ`, for `τ` extending `σ`. FAG's compatibility of restriction with further pullback (`cohomologyPresheafRestrict_comp'`) is a natural starting point for (d), but FAG does not state (d). With F1 and F2 the result is then compared with the Library's `Hⁿ`, its universes and `galoisCohomologyRep`.
- **F4, spreading out, and the coefficients and base for specialization.**
  - *The model.* A smooth proper model of `X` over a ring of `T`-integers is an assembly of Library results, the same as for Stacks (bridge B3, statements A.5): `numberFieldSpreadSeparatedExistence`, then `numberFieldSpreadEventualSmoothness` and `numberFieldSpreadEventualProperness` applied to the structure morphism of the model, then base change to a common level, as in `exists_numberFieldSmoothConnectedModel` for the geometrically connected case. FAG's own spreading-out lemmas, such as `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit` (`AlgebraicGeometry/EventuallyProper.lean:70`), are not needed for this, and FAG has no assembled statement.
  - *Coefficients and base for one finite module `M`.* FAG's specialization theorems (`SmoothProperLocallyConstant.lean:153`, `:180`; statements C.1) take `Λ : Type (u + 1)` with `N ≠ 0`, `(N : Λ) = 0`, and `N` a unit on the base: `IsUnit (N : Γ(Y, ⊤))`, or, on a strictly local base `Spec A` (FAG's variable is called `R` there), `IsUnit (N : Γ(Spec A, ⊤))`. The premise allows any commutative `R` and tests only places `v` with `e = Nat.card M ∉ v`. Take `Λ = ULift (ZMod e)`. `M` is a `ZMod e`-module, because `e • M = 0`, and its constant sheaf is locally constant (instance at `ConstructibleSheaf/DenseOpenUnit.lean:227`). The Library's cohomology of `M` as a sheaf of `R`-modules must be identified with FAG's cohomology of the lifted sheaf of `Λ`-modules, naturally and compatibly with pullbacks (F1). Both are the cohomology of the underlying abelian sheaf (the argument of `EtaleGaloisGoodReduction/Statement.md`, step 2; inside FAG, `bijective_mapExtComp_constantIntToRing`, Section 5.2). For the base, apply `…_upperStar_homology_of_smooth_of_isProper` on the base change of the model to the level `T ∪ numberFieldPrincipalExceptional K e`, where `e` is a unit (B3). Or apply `…_homology_lowerStar_of_smooth_of_isProper` to the strict henselization at a geometric point over `v`, where `e` is a unit because `e ∉ v`. In both cases `v` is a point of the base used, so the finite set `S = T` comes from the model and does not depend on `M`. On the model's own base the hypothesis can fail: for `K = ℚ`, a model over `Spec ℤ` and `M = ℤ/2`, the integer `2` is not a unit on `Spec ℤ`, although the premise asks about the place `3`.
  - *The Harris stages.* As in B3: `A_r` is killed by a power `p^{a_r}` (its stalks have `p`-power order), so take `Λ_r = ULift (ZMod (p^{a_r}))`. On the one open `Spec 𝒪_F[1/pN]` of B3′, `p` and hence every `p^{a_r}` is a unit, so FAG's theorem applies to every stage on that one open.
  - *The uniform extension.* For Harris, the model must carry every coefficient stage at once: one open `Spec 𝒪_F[1/pN]` with locally constant constructible extensions `𝒜_r` of all the `A_r`, because `HarrisCMCohomologyUnramifiedStatement` chooses `S` before `r`. Spreading each `A_r` separately gives an open depending on `r`. This uniform extension is bridge B3′ of Section 4.4, with the route that the Library's `HarrisCMCohomologyUnramified/Statement.md` describes (universal abelian scheme over a model, monodromy controlled by `p`-power torsion, descent along `π_1`). FAG's specialization theorems apply only after `𝒜_r` is given.
- **F5, inertia.** From the specialization isomorphism at the strict localization at `v` of the base of F4 on which `e` is a unit, to `DecompositionGroupAction.IsUnramifiedAt`. That predicate is about the inertia subgroup of the completion, the kernel of its residue action, restricted along Mathlib's chosen embedding of `K̄` into an algebraic closure of `K_v`. FAG supplies much of the step. First, over any base (statements C.11):
  - the cospecialization map of the higher direct images of a smooth proper morphism is bijective. `bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap` (`SixFunctors/Etale/BaseChangeTheorems/CospecializationSections.lean:283`) states, for any sheaf `G` of `Λ`-modules on any `Y`, a geometric point `s` of `Y` with strict localization `g : Y_(s) ⟶ Y` and a geometric point `t` of `Y_(s)`: if restriction of sections `Γ(Y_(s), g^*G) ⟶ Γ(Spec Ω', t^*g^*G)` is an isomorphism, then the cospecialization map `G_s ⟶ G_{t ≫ g}` is bijective. For `G = Rᵠf_*F`, with `f` smooth and proper, `F` locally constant and `Λ` killed by an integer `N ≠ 0` invertible on `Y`, the hypothesis is `SmoothProperLocallyConstant.lean:180`. FAG combines the two in this way at `:241-247`, in the proof of its local-constancy form over a field, but the combination uses no field. The map is `cospecializationMap` (`AlgebraicGeometry/Sites/Cospecialization.lean:215`): the germ at a pointed étale neighbourhood `(V, v)` of `s` goes to the germ at `t` followed by the leg `Y_(s) ⟶ V`.

  Second, in global Galois terms, FAG's setting is a maximal ideal `Q` of the integral closure `B` of a domain `R` in a separably closed Galois extension `Ω` of `K = Frac R`, with inertia group `Q.inertia ⊆ Gal(Ω/K)` (statements C.7):
  - the specialization map `boundarySpecialization` (`EtaleCohomology/Purity/RealSheaves/BoundaryStalk.lean:91`) goes from the stalk of `j_*F` at the closed geometric point of `Spec B_Q` to the generic geometric stalk of `F`, for an open immersion `j : U ⟶ C` into an integral scheme. Its image is fixed by `Q.inertia` for any sheaf `F` on `U` (`galoisStalkMap_boundarySpecialization`, `:196`). Under further hypotheses, among them `F` finite locally constant, `Λ` finite, `U` connected, a Dedekind ring of sections and a perfect residue field, FAG identifies the image with the inertia invariants (`range_boundarySpecialization`, `:319`); the route does not need this. The map is injective for a locally constant sheaf when the base is locally noetherian and its étale local rings are domains (`injective_specializationStalk`, `ConstructibleSheaf/LowerStarSpecialization.lean:310`);
  - `Q.inertia` acts trivially on the geometric generic fibre of every finite étale scheme over a connected scheme `Y` with a morphism `Spec R ⟶ Y` (`galoisToAut_hom_app_eq_of_mem_inertia`, `FundamentalGroup/DecompositionGroup.lean:73`), and a finite locally constant sheaf of sets is the sheaf of sections of a finite étale scheme (`exists_iso_uliftYoneda_of_isFiniteLocallyConstant`, `FiniteLocallyConstantEtale.lean:227`);
  - the ring of `Q.inertia`-invariants `B_Q^{I_Q}` is strictly henselian (`RingTheory/InertiaIndEtale.lean:70`); for a Dedekind `R`, its localization away from a nonzero element of `Q ∩ R` is the fixed field of `Q.inertia` (`:551`), and it is ind-étale over `R` when the residue field at `Q ∩ R` is perfect (`:602`).

  Third, the two maps can be placed at the same pair of points (statements C.12). `B_Q` is strictly henselian when `R → Ω` is injective (`Ideal.isStrictlyHenselianLocalRing_atPrime`, `RingTheory/StrictlyHenselianNormal.lean:73`). For a geometric point `s : Spec Ω ⟶ S`, a strictly henselian local `Spec B` over `S` with a geometric point `p₀` over `s` and over the closed point maps to `S_(s)` over `S`, carrying `p₀` to the canonical geometric point (`exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing`, `AlgebraicGeometry/Sites/StrictLocalizationUniversal.lean:168`), and such a map is unique (`hom_strictLocalization_ext`, `:132`). The germ formulas are `toPresheafFiber_cospecializationMap` (`Cospecialization.lean:225`): the germ at a pointed étale neighbourhood `(V, v)` of `s` goes to the germ at `(V, t ≫ (S_(s) ⟶ V))`; and `toPresheafFiber_specializationStalk` (`ConstructibleSheaf/LowerStarSpecialization.lean:245`): it goes to the germ at `specializationFiber V v`, the lift of `η` through the unique lift `Spec A ⟶ V` of `v` (`:134`). `boundarySpecialization` is `specializationStalk` with `A = B_Q`, `a = specAtPrime Q` and `ι = atPrimeToField Q` (`BoundaryStalk.lean:95`).

  What remains: (a) the comparison of the two maps. Take for `Y = C = U` the base of F4 on which `e` is a unit, `j = 𝟙`, the sheaf `Rⁿf_*M` of `ULift (ZMod e)`-modules, `s` the closed geometric point of `Spec B_Q` for `Q` over `v`, `k : Spec B_Q ⟶ Y_(s)` the morphism given by the universal property, and `t = Spec Ω ⟶ Spec B_Q ⟶ Y_(s)`. Then `t ≫ (Y_(s) ⟶ Y)` is the generic geometric point `η` used by `boundarySpecialization`, but only up to an equality of morphisms, so the two stalks are identified by transport along it. One must show that the cospecialization map at `(s, t)` agrees with `boundarySpecialization`, after `(𝟙)_*F ≅ F` and that transport. By the germ formulas this reduces, for each `(V, v)`, to the equality of the two points of `V` over `η`: `t ≫ (Y_(s) ⟶ V)` and the point of `specializationFiber V v`. Both come from morphisms `Spec B_Q ⟶ V` that lift `v` (the first is `k` followed by the leg of `Y_(s)`), so FAG's uniqueness of such lifts (`henselianLift`; `lift_ext_of_comp_eq`, `StrictLocalizationUniversal.lean:47`) should give it. FAG does not state this comparison. Then the cospecialization map is bijective with image fixed by `Q.inertia`, so `Q.inertia` fixes the whole generic geometric stalk; (b) the Galois-equivariant identification of the generic geometric stalk of `Rⁿf_*M` with `Hⁿ(X_K̄, M)` and the Library's `galoisCohomologyRep`: route (ii) of F3 at the generic point; (c) for `Q` over `v`, the identification of `Q.inertia` with the Library's local inertia through Mathlib's embedding. We did not find (a)–(c) in FAG or in the Library. For the Stacks repository, see bridge B4, which also lists its inertia results.
- **F6, the Harris coefficients.** `B_r` locally constant / constructible in FAG's sense, from the Library's trivializations (`cmHarrisCoefficientSystemTrivialization`, `cmHarrisCoefficientEtaleDiagram_coversTop`).

### 5.5 Item 3: can FAG alone supply the premises that are needed?

Mathematically yes for the premises on the route of Kottwitz's varieties: good reduction
(specialization over strictly henselian bases of any characteristic, with proper base change),
Galois smoothness, including the level-colimit statements (09YQ through the Library's own
action, or 03Q9 through the Galois point; bridge F3), and finiteness for proper varieties over
a separably closed field. It does not supply `GaloisCohomologyUnramifiedStatement`, the unramified
statement for varieties of finite type that need not be proper, and neither does the Stacks
repository. FAG has generic base change only over an integral base of finite type over a
field, for an open immersion or for a smooth source with finite locally constant coefficients
(Section 5.3). Neither form reaches an open of `Spec 𝒪_K`, and that premise is not on the
route (Section 6). Compared with the Stacks repository, FAG lacks a Galois-equivariant `RΓ` of
a base-changed scheme. So smoothness needs bridge F3. The first option is the limit argument
through the Library's action, for which FAG has the cone, 09YQ for `Sheaf.H` and the
composition rule, so that only the comparisons F1 and F2 and the lift of the cone to a slice
remain. The second is the stalk formula with the discrete-module equivalence, whose action
must still be identified with the geometric one. It covers the separable closure, and the
algebraic closure after a transport, but not an arbitrary algebraic extension. FAG's
coefficient ring also sits one universe higher than the Library's. For good reduction its
specialization theorem needs coefficients killed by an integer `N` that is a unit on the
base. So the premise's module `M` over an arbitrary `R` is moved to `ULift (ZMod e)`,
`e = Nat.card M`, and the theorem is applied on an open, or a strictly local base, where `e`
is a unit. The finite set of places still comes from the model alone (F4). The model
itself is an assembly of the Library's own number-field spreading theorems (B3, F4). Both libraries have inertia results that cover part of the step to
`IsUnramifiedAt` (bridges F5 and B4). FAG's cospecialization bijectivity covers the
specialization part over that base, and its universal property of the strict localization
and its germ formulas place the cospecialization map and its inertia-invariant specialization
map at the same points; what remains there is to prove that the two maps agree, to identify the
generic stalk equivariantly with `Hⁿ(X_K̄, M)`, and to compare the global inertia group with the
Library's. In every case
the bridges F1–F6 remain to be proved; for the Harris unramified statement this includes the
uniform extension of all coefficient stages over one open (F4), which neither library supplies.
Practically FAG is not usable at the Library's pin today (focused compile below), and its
closures are large.

### 5.6 Item 5: reuse-rule facts for FAG

The closures were computed with a script that reads source text only: imports parsed
from the headers of the module files, closure inside the repository (`WeilConjectures/*` and
`Comparator/*`), comments and string literals blanked before the text scan. The method, every
hit and the full lists are in
[`fag-scan-report.md`](etale-premises-sheaf-libraries-evidence/fag-scan-report.md). The
figures below are from a second run. The first run read each
header line by line, so it missed an import command wrapped across lines and every later import
of the same file. 31 FAG files and 1,161 Stacks files have such wrapped imports. The second run
reads the header as a token sequence. It enlarged the premise closure from 7,255 to 7,275
modules and the union of the Laumon closures from 16,814 to 16,839. The earlier figures are
in brackets in the scan report. Lines are counts of newline characters, as for Stacks in
Section 7.1. An earlier count of the FAG lines counted one more line per file, for
example 103,409 instead of 102,942 for the 467 modules of `CohomologyLimit`. The module
counts are unaffected.

| Root (`WeilConjectures.…`) | Repository modules | Lines | Mathlib modules imported directly | `sorry` sites in closure |
|---|---|---|---|---|
| `SixFunctors.Etale.BaseChangeTheorems.SmoothProperLocallyConstant` | 7,258 | 1,245,786 | 1,577 | 0 |
| `SixFunctors.Etale.BaseChangeTheorems.Proper` | 6,978 | 1,191,229 | 1,565 | 0 |
| `SixFunctors.Etale.BaseChangeTheorems.Smooth` | 6,561 | 1,122,976 | 1,550 | 0 |
| `SixFunctors.Etale.Derived.Finiteness.Proper` | 7,050 | 1,204,390 | 1,569 | 0 |
| `AlgebraicGeometry.Sites.CohomologyLimit` | 467 | 102,942 | 603 | 0 |
| union of the five (premise roots) | 7,275 | 1,252,455 | 1,578 | 0 |
| Laumon roots, the FAG modules that Laumon's theorem needs (`TraceFormula.Specialization.NearbyFiniteness`, `SixFunctors.NearbyCycles.GaloisAction`, `FourierTransform.Inversion`, `WeilSheaf.FourierInversion`, `WeilSheaf.WeilFourierInversion`) | 14,545; 13,484; 8,460; 16,818; 13,533 | | | 11; 11; 1; 14; 13 |
| union of the five Laumon roots (the Laumon closures) | 16,839 | 3,494,755 | 1,935 | 17 |
| `Statement` (headline Weil conjectures) | 17,339 | 3,610,380 | 1,991 | 14 |
| whole repository (`WeilConjectures`, `Statement`) | 26,796 | 5,482,914 | 2,186 | 209 |

The union of the five Laumon roots contains all but 19 of the 7,275 premise
modules. The 19 are `AlgebraicGeometry.Sites.CohomologyLimit` (09YQ) and fifteen
modules under it (an Ext resolution, étale and semi-simplicial hypercovers,
hypercover descent, limits of upper-star sections, `Sites.LocallyExact`), and
the three `BaseChangeTheorems` modules `Smooth`, `SmoothProperLocallyConstant`
and `SmoothProperSpecialization`. They are the same 19 modules with both parsers. The
count was made from the module lists, checked, and recounted
with the second parser. The scan report names all 19.

In the premise closures there is no `sorry`, `admit`, axiom declaration, `sorryAx`,
`native_decide`, `decide +native`, `debug.skipKernelTC`, `ofReduceBool`, `implemented_by`,
`extern`, `unsafe`, `opaque`, `#eval` or `maxHeartbeats 0`. There are six `run_tac` calls inside
proofs, and two local `macro_rules` for the tactic `lia`. The sixth `run_tac`, found only by
the second run (`AlgebraicGeometry/HigherDirectImageRawTransitionToHomCore.lean:257`), builds
a congruence proof whose result the kernel checks. The larger closures also contain `WeilConjectures/Tactic/FirstOrderApply.lean`, whose
tactic adds theorem declarations with `addDecl (.thmDecl …)` (kernel-checked) and keeps an
`IO.Ref` (`initialize`). A `sorry` site in a closure does not mean that a root depends on it (the
headline closure contains 14, which the README says the main theorem does not use; e.g.
`WeilSheaf/SmoothPurity.lean:298` is documented as unused); only `#print axioms` after a build
settles it, and `warn.sorry = false` hides the warnings.

**Modules cited for statements C.5–C.9.** The same script was run on the twelve
modules that Sections 5.3 and 5.4 cite (the scan report's section "Modules cited for
statements C.5–C.9" has the table and the module lists). The closure of
`SixFunctors.Etale.Derived.Finiteness.Deligne` (FAG's generic base change over a field, both
forms) has 8,230 modules, 979 of them outside the premise closure and none outside the union
of the premise and Laumon closures. The module of the prime-field smooth-source form,
`AlgebraicGeometry.SmoothGenericDirectImage`, lies inside that closure.
`AlgebraicGeometry.Sites.GaloisModule` (81 modules),
`AlgebraicGeometry.GeometricFrobenius` (4), `FundamentalGroup.DecompositionGroup` (68),
`AlgebraicGeometry.FiniteLocallyConstantEtale` (113) and
`AlgebraicGeometry.Sites.StrictHenselizationField` (5) lie inside the premise closure, and so
does FAG's 03SI, `SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`. The
other modules reach slightly beyond the union of the premise and Laumon closures; the
second number counts the modules outside it: `RingTheory.InertiaIndEtale` (37 modules, 6
outside), `ConstructibleSheaf.LowerStarSpecialization` (310, 2 outside),
`EtaleCohomology.Purity.RealSheaves.BoundaryStalk` (4,051, 27 outside),
`FundamentalGroup.CurveDualTateModule` (5,801, 52 outside), which is cited only for the
Galois automorphisms of a geometric fibre,
`SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.StalkFormula` (03Q9; 967, 2 outside) and
`AlgebraicGeometry.EtaleSheafDiscreteContinuousRep` (97, 4 outside). The roots of route (ii)
of F3 (`StalkFormula`, `StrictHenselizationField`, `GaloisModule` and
`EtaleSheafDiscreteContinuousRep`) together have 987 modules, 6 of them outside the union of
the premise and Laumon closures. All twelve roots together with the five premise roots
have 8,449 modules, 68 of them outside that union. None of these closures has a `sorry` site.
Their other hits are `run_tac` blocks inside proofs (33 in the `Deligne` closure: the six
above and 27 others, which were not read one by one), the two `lia` macros above, and
`set_option backward.…` lines.

**Nine further cited modules.** Nine more roots are cited for bridges F3 and F5 and
for the comparisons of Section 5.2 (the scan report's section of the same name has the
Mathlib and scan columns). The table gives the number of repository modules in the
closure, its lines, and the numbers of modules outside the premise closure (P) and outside the
union of the premise and Laumon closures (P ∪ T).

| Root (`WeilConjectures.…`) | Modules | Lines | Outside P | Outside P ∪ T |
|---|---|---|---|---|
| `AlgebraicGeometry.IntermediateFieldLimit` | 1 | 280 | 1 | 0 |
| `SixFunctors.ProEtale.GaloisAcyclic.FieldExtension` | 1,190 | 230,162 | 88 | 0 |
| `WeilSheaf.CondensedModelFiniteLevelColimit` | 706 | 163,078 | 243 | 1 |
| `AlgebraicGeometry.Sites.CohomologyContinuity` | 947 | 187,882 | 0 | 0 |
| `SixFunctors.Etale.BaseChangeTheorems.CospecializationSections` | 468 | 102,340 | 0 | 0 |
| `AlgebraicGeometry.Sites.StrictHenselizationLocal` | 2 | 798 | 0 | 0 |
| `AlgebraicGeometry.Sites.FieldCohomologicalDimension` | 5,217 | 907,455 | 0 | 0 |
| `SixFunctors.Etale.ConstantCohomologyExt` | 7,083 | 1,209,309 | 71 | 1 |
| `SixFunctors.Etale.ForgetModuleCohomology` | 1,097 | 215,501 | 62 | 0 |

In the two rows with one module outside P ∪ T, that module is the root itself. The module
of the composition rule, `AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`, lies in
the premise closure. The twelve roots of the previous paragraph, the five premise roots and
these nine have 8,550 modules (1,539,264 lines), 70 of them outside P ∪ T. Without
`CondensedModelFiniteLevelColimit`, which only exports the cone for an algebraic closure, they
have 8,466 modules (1,515,233 lines), 69 outside. None of the nine closures has a `sorry`
site. `ConstantCohomologyExt` has the six `run_tac` blocks and two macros of the premise
closure, and the union has the 33 `run_tac` blocks of the `Deligne` closure. The nine
module counts, the counts outside P ∪ T and both unions with their lines were recounted
with separate tools, with the same values.

**Two modules cited for bridge F5.** Two more roots are cited for bridge F5 (statements
C.12). The same script was used, and the scan report has a section of the same name:

| Root (`WeilConjectures.…`) | Modules | Lines | Outside P | Outside P ∪ T |
|---|---|---|---|---|
| `AlgebraicGeometry.Sites.StrictLocalizationUniversal` | 592 | 129,730 | 3 | 0 |
| `RingTheory.StrictlyHenselianNormal` | 7 | 1,611 | 0 | 0 |

With them the union of all cited FAG roots and the premise roots has 8,553 modules
(1,540,119 lines), of which 1,278 lie outside P and 70 outside P ∪ T, the same 70 as before.
The germ formulas cited in F5 are in modules already counted (`Cospecialization`,
`LowerStarSpecialization`, `BoundaryStalk`).

**Focused compile on the Library's pin.** Lean 4.34.0, Mathlib `5ed2965`, entry `WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit`
with its 467 repository modules copied unchanged (byte-identical to the pin; aggregate SHA-256
`3b91f83a…`, defined in the scan report):
**fails**. Lake built 190 modules and 70 failed with 346 errors (50 modules of
`WeilConjectures/Mathlib` with 200 errors, 10 of `FromJoel` with 80, 10 others with 66). The
other 207 were not built, so 346 is a lower bound. Two directly imported Mathlib modules do not
exist at `5ed2965` (`Mathlib.Order.Int.ConditionallyCompleteOrder`, there
`Mathlib.Data.Int.ConditionallyCompleteOrder`; `Mathlib.CategoryTheory.Functor.Quadrifunctor`).
The other errors come from FAG's newer Mathlib: 13 unknown constants, identifiers or fields
(such as `AlgHom.toRingHom_injective` and `CategoryTheory.End.mul_asHom`), 85 unsolved goals, 57
failed rewrites, 31 instance failures, and 37 kernel errors, 25 of them in `FromJoel`. The scan
report lists the 70 modules with their error counts. No edits were attempted: at this count,
taking FAG down to the Library's pin is a port, which this audit does not start. A
separate function-level probe (three modules of `FourierTransform.Classical`) compiles
unchanged, which shows that the module syntax itself is not
the obstacle.

## 6. Is generic base change needed? (item 4)

No, provided the uniform extension of the coefficients (bridge B3′, F4) is
proved. Deligne's generic base change is the source only of
`GaloisCohomologyUnramifiedStatement`, which concerns varieties of finite type
that need not be proper. That statement has no Lean consumer (Section 2.3). The
route's unramified statement is `HarrisCMCohomologyUnramifiedStatement`. It is
about `X̄_U`, which the Library proves smooth and proper (Section 2.2), with
locally constant coefficients `B_r`, on which multiplication by `m^r` is zero.
It requires one finite set `S` for every degree and every stage `r`.
Specialization for smooth proper morphisms (SGA 4 XVI 2.1–2.2) gives it, once
there is one open `T' = Spec 𝒪_F[1/pN]`, a smooth proper model of `X_U` over
`T'`, and on that model locally constant constructible extensions `𝒜_r` of
every `A_r` at once. Spreading `X_U` and each `A_r` out separately is not
enough: the open would depend on `r`. The model of `X_U` alone is an assembly
of the Library's number-field spreading theorems (bridge B3). The Library's documentation of the
statement (`Langlands/Cohomology/HarrisCMCohomologyUnramified/Statement.md`,
"Why the statement is expected to hold") gives the uniform construction:
extend the universal abelian scheme over a model chosen once, bound the
monodromy of every coefficient cover by its `p`-power torsion, and descend
every `A_r` along `π_1` (SGA 1 V 8.2). Its finite set `S` is the set of places
dividing `pN`. Each stage has `p`-power order, so outside `S` the torsion is
prime to the residue characteristic. `N` is chosen once, so `S` does not depend
on `degree` or `r`. Neither library contains this construction. Both supply
the specialization theorem that is applied after it: Stacks 0GLI and 0GKD, and
FAG `…_of_smooth_of_isProper`. The coefficients are `ZMod (p^{a_r})` for Stacks
and `ULift (ZMod (p^{a_r}))` for FAG, where `p^{a_r}` kills `A_r`. They are
used on the one open where `p` is a unit (B3, F4).

The general `GaloisCohomologyGoodReductionStatement` gives
`GaloisCohomologyUnramifiedStatement` for smooth proper `f` by a short
derivation, which neither library needs to supply. For a fixed finite `M`, only
finitely many `v` contain `Nat.card M`, so the set `S ∪ {v | (Nat.card M : 𝒪_K) ∈ v.asIdeal}`
is finite. Generic base change is needed only if a later consumer requires the
unramified statement for a variety that is not proper. Neither library has it
in the form that consumer would need. Stacks has only special cases
(Section 4.4). FAG has it over an integral base of finite type over a field,
for an open immersion and for a smooth source with finite locally constant
coefficients (Section 5.3). Neither form applies over an open of `Spec 𝒪_K`.
Whether FAG's proofs extend to such a base was not examined.

## 7. Reuse-rule facts for Stacks (item 5)

### 7.1 Closures and scans

The closures follow the import commands of the module headers inside the
repository. Lines are newline counts. A first version of
the table was computed with `closure.py`, stripping comments and string literals
before the text scan, and the union and the two extra roots were recomputed with
a separate script. That version read each header line by line and missed import
commands wrapped across lines, which occur in 1,161 Stacks files (for example
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmoothProperHigherDirectImageLocallyConstantReduction.lean:3-25`).
Every figure was then recomputed with a parser that
reads the header as a token sequence, and both unions and the rows for 09YQ, `SmallEtaleColimitUnconditional`, the action
identification and spreading out were recounted independently, with the same
results.

| Root (`StacksFrontier.AlgebraicGeometry.EtaleCohomology.…`) | Repository modules | Mathlib modules imported directly |
| --- | --- | --- |
| `SmoothProperHigherDirectImageLocallyConstant` (0GLI) | 17,744 (5.38M lines) | 2,242 |
| `LocalAcyclicity.SmoothProperSpecializationUnconditional` (0GKD) | 16,009 (4.86M lines) | 2,182 |
| `DerivedLowerShriek.CompactSupportFinitenessAlgClosed` (0GLH) | 17,353 (5.26M lines) | 2,239 |
| `DerivedLowerShriek.ConstructibilityUnconditional` (0GL0) | 17,291 (5.24M lines) | 2,235 |
| `Colimits.QcqsEtaleCohomologyColimit` (09YQ) | 1,215 | 1,046 |
| `Colimits.SmallEtaleColimitUnconditional` | 2,369 | 1,418 |
| `Trace.GaloisEquivariantDerivedGlobalSections` (Galois `RΓ`) | 4,763 (1.50M lines) | 1,728 |
| `Trace.GaloisEquivariantCohomologyAction` (action identified) | 7,795 (2.40M lines) | 1,912 |
| `StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.ProperSmoothFiniteTypeSubring` (spreading out) | 2,946 (0.87M lines) | 1,404 |
| union of the first seven roots | 17,881 (17,435 Frontier + 446 Core; 5,428,499 lines) | 2,247 |
| union of all nine roots | 17,890 (17,444 Frontier + 446 Core; 5,431,335 lines) | 2,247 |

The sorted module list of the nine-root union (one name per line, LF line endings) has
SHA-256 `dce55507be9360c59ad35ea7ad000a6a1f675d8b51b720df4c42b75d4a268b64`. Earlier versions
of this table gave 16,918 and 16,929 (line-by-line parser), and before that 16,919 and 16,930.
The last two came from a root set that had `ProperBaseChange.ProperBaseChangeStacksTags` (095T)
in place of 09YQ. That module has 51 lines and only attaches Stacks tags, so it declares no
constants.

**Roots cited for statements B.9–B.11.** The same script was run on the roots that Sections
4.1, 4.2 and 4.4 cite (statements B.9–B.11). The nine-root union and its digest were
reproduced in the same run.

| Root | Repository modules | Lines | Mathlib modules imported directly | Outside the nine-root union |
| --- | --- | --- | --- | --- |
| `…EtaleCohomology.Colimits.AlgebraicExtensionCohomologyColimit` (09YQ over an algebraic extension) | 2,372 | 758,474 | 1,418 | 2 |
| `StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.FiniteTypeModel` (spreading out with `Smooth`) | 1,922 | 563,111 | 1,215 | 0 |
| `…EtaleCohomology.SmoothProperHigherDirectImageLocallyConstantReduction` (0GLI over an affine base) | 17,743 | 5,384,114 | 2,242 | 0 |
| `…EtaleCohomology.Constructible.FiniteLocallyConstantLimit.EssSurj` (0GL2) | 1,362 | 368,488 | 1,036 | 0 |
| `StacksFrontier.CategoryTheory.Sites.Cohomology.CoefficientUniverseLift` | 1 | 319 | 16 | 0 |
| `…EtaleCohomology.SmallEtaleCoefficientLift` | 788 | 185,821 | 859 | 0 |
| `StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived` | 1,800 | 552,295 | 1,283 | 0 |
| `StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison` (03FD) | 5 | 1,999 | 26 | 0 |

The two modules outside the nine-root union are the root `AlgebraicExtensionCohomologyColimit`
(153 lines) and `Colimits.PullbackSystemCohomologyColimit` (387 lines), which it imports. Neither
contains any of the scanned patterns. With this root the union has 17,892 modules.

Text scan of the union (the same hits for seven and for nine roots):

- **Absent:** `sorry`, `axiom`, `sorryAx`, `native_decide`, `decide +native`,
  `debug.skipKernelTC`, `ofReduceBool`, `implemented_by`, `extern`, `unsafe`,
  and `addDecl`/`mkAxiom`. The one `admit` hit is inside a string
  (`StacksFrontier/AlgebraicGeometry/Topologies/ExtendingFunctors.lean:324`, an attribute text).
- **`noncomputable opaque standardOpenBaseChange`** occurs once
  (`StacksFrontier/RingTheory/GradedAlgebra/Proj/StandardOpenBaseChange.lean:999`).
  An `opaque` declares a constant with a kernel-checked inhabitant, not an axiom.
- **Metaprogramming commands:** `run_meta` at `StacksFrontier/AlgebraicGeometry/Descent/Scheme/PulledBackDatum.lean:1098`
  clears an auxiliary-lemma environment extension during elaboration, and the
  kernel still checks the declarations. `run_cmd` at `StacksFrontier/AlgebraicGeometry/Scheme/Affine/Sections.lean:63`
  only builds an attribute command. `run_tac` at
  `StacksFrontier/AlgebraicGeometry/Crystalline/ExplicitDividedPower/Formula.lean:532`
  calls `Mathlib.Tactic.Module.matchScalars`, the core of the `module` tactic, to
  split the goal; the kernel checks the resulting proof. There are also 17
  syntax, macro or elaborator definitions in 6 files, which were not read one
  by one.
- **Options and initializers:** three `initialize` in `StacksCore/Tactic`, which
  register attributes; one `set_option maxHeartbeats 0`
  (`StacksFrontier/RingTheory/Branches/MinimalPrimes.lean:477`); and 1,251
  `set_option backward.*` lines in 487 files. These are elaboration options.
- **`lakefile.toml`** has no option that silences `sorry`.

A text scan does not replace `#print axioms` after a build, which has not been
run on any premise root.

### 7.2 Focused compiles on the Library's pin

Both compiles used Lean 4.34.0 and Mathlib `5ed2965` through the project's
Lean checking service with Lake build, each on a copy
in a private draft directory.

1. **Sample 1.** 13 unmodified Stacks files: `StacksCore.Tactic.{EgaSgaAttribute,StacksAttribute}`
   (including `initialize`), `GeometricPoint`, `GaloisActionStalks.Basic`,
   `NeighborhoodsStalksPoints.Basic`, `OpenSubgroupFixedField`,
   `SliceConstantSheaf`, `Comparison.DerivedFunctor`, `SliceAdjunctions`,
   `Sites.Modules.ExtensionByZero`, `DiscreteCochains` and
   `Sheafification.SmallEtale{Abelian,Colimits}`. Result: 0 errors, 0 warnings.
2. **Sample 2.** The full import closure of
   `StacksFrontier.AlgebraicGeometry.EtaleCohomology.{SmallEtaleModuleDerivedFunctors, ComparingBigSmall.SheafCohomology, EtaleModulesConstantRing}`.
   These root modules define `EtaleModules`, its derived functors, the
   comparison of big-site and small-site cohomology, and constant-ring modules.
   The closure has 318 modules (289 Frontier and 29 Core) and 122,942 lines. The
   aggregate SHA-256 of the originals is `e42cb7931cd7…`; of the adapted files,
   `573f0528f88f…` (full values and per-file hashes in the manifest).

| Run | Result |
| --- | --- |
| 1 | after 21 import renames: 21 errors, 3 warnings, in 6 modules; dependants skipped |
| 2 | 13 errors in 3 modules |
| 3 | 6 errors in 2 modules |
| 4 | 1 error |
| 5 | 1 error, with a heartbeat increase to 10⁶, which was then reverted |
| 6, 7 | test variants of the last fix |
| **8** | **0 errors, 0 warnings; all 318 modules and the three roots built** |

The final edit set touches 30 of the 318 files and adds 95 lines while
removing 48. It is listed in full in
[`stacks-sample2-edits.md`](etale-premises-sheaf-libraries-evidence/stacks-sample2-edits.md).

| Kind | Files | Edit |
| --- | --- | --- |
| Mathlib module renamed between the pins | 21 | imports only: `Mathlib.Order.Int.*` → `Mathlib.Data.Int.*`, `Mathlib.Algebra.Order.Star.Int` → `Mathlib.Data.Int.Star`, `Mathlib.Order.SuccPred.Int` → `Mathlib.Data.Int.SuccPred` |
| Mathlib lemma absent at `5ed2965` | `StacksCore/CategoryTheory/Subobject/Limits.lean` | five declarations copied from Mathlib `56a0058`: `imageSubobject_comp_of_strongEpi`, `exists_eq_imageSubobject` and `exists_mk_eq_imageSubobject` (Mathlib PR 42759), plus `exists_pullback_eq_inf_of_mono` and `pullback_kernelSubobject` |
| Mathlib lemma renamed | `StacksFrontier/Homology/Perfect/FibreCriterion/{BaseChangeSurjective,FibreCohomologyVanishing}.lean` | `LinearMap.baseChange_eq_lTensor` → `baseChange_eq_ltensor` |
| changed signature | `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ULiftUnit.lean:494` | `ULift.ext _ _` |
| `simp` lemmas that no longer fire | `StacksFrontier/AlgebraicGeometry/Topologies/EtaleDescentIntegral.lean:251–361`, `…/Topologies/EtaleUniversalHomeomorphism.lean:130` | explicit `pullback.lift_fst`/`pullback.lift_snd` |
| `End` is a `def` at `5ed2965` | `StacksFrontier/CategoryTheory/Triangulated/Elementary.lean:172` | direct application of the lemma |
| leftover goal `0 = 0` | `StacksFrontier/Homology/Injectives/KInjective/SmallAcyclicComplexes.lean:303` | `<;> rfl` |
| instance unification | `StacksFrontier/Homology/Perfect/ProjectiveAmplitude.lean:860, 878` | explicit `of_equiv` arguments; `have h := …; exact h` |

No edit changes a statement, except the five backported Mathlib lemmas, which
keep their Mathlib statements. No heartbeat option was changed.

Sample 2 covers 318 of the roughly 17,900 modules that the premises need. Edits
were needed in 9.4% of its files, and proof-level edits in 2.8%. Extrapolating
these rates to the premise closure is not reliable, and the closure was not
compiled. Under the plan note's configuration B, with the Library on
`56a0058`, the question of adapting Stacks to the Library's pin does not arise.

## 8. One module importing both closures (item 6)

At their common pin (Lean 4.35.0, Mathlib `56a0058`) the two repositories have the same
dependencies and disjoint module roots (`StacksCore`, `StacksFrontier`, `Stacks` against
`WeilConjectures`, `Weil`, `LeanEvalWeil`), so a Lake project can require both. One module
cannot import the closures used here, because they declare the same names.

**Shared names.** The public declaration names were extracted from the source text of the
Stacks union of the seven premise roots (Section 7.1; 17,881 modules) and of the FAG union of
the five premise roots and the five Laumon roots (16,858 modules). Namespaces were followed,
`private` declarations skipped, and names that Lean generates (unnamed instances, projections,
auxiliary lemmas) were not produced, so the count is a lower bound. **332 names are declared in
both**, 286 of them in the FAG premise closure. On the FAG side 180 are in its own files, 137 in
`WeilConjectures/Mathlib` and 15 in `WeilConjectures/FromJoel`. On the Stacks side 304 are in
`StacksFrontier` and 28 in `StacksCore`. All 332 are public on both sides under the module
system. The first count, 327 names, came from the closures of the line-by-line parser
(Sections 5.6 and 7.1); all 327 reappear in the corrected list, which adds five. Eight were checked by hand. Examples: `AlgebraicGeometry.HasCompactification` is a class in FAG
`Compactification/Defs.lean` and a def in Stacks
`AlgebraicGeometry/NagataCompactification/HasCompactification.lean`, and the two
`AlgebraicGeometry.relativeFrobenius` take different arguments. So the shared names cannot simply
be merged. The list, with the modules on each side and the method, is
[`co-import-name-clashes.md`](etale-premises-sheaf-libraries-evidence/co-import-name-clashes.md).

**Which of them Lean rejects.** Lean does not reject every name that two imported modules both
declare. Lean 4.34 accepts the pair when both declarations are theorems with the same
elaborated statement and the same universe parameter names; an instance of a
proposition-valued class counts as a theorem. Any other pair makes the import fail. The
rule was confirmed on five test modules in the project's Lean service (described in the
evidence file). The rule
also explains why Stacks can declare 35 names twice inside its own premise closure: all 35 are
theorems, lemmas or instances. Of the 332 shared names, **113 (99 of them in the FAG premise closure)
are rejected whatever the statements**, because on at least one side the declaration is a
`def`, `abbrev`, `class` or `structure`, or an instance of a class with data
(`AlgebraicGeometry.ProjectiveSpace.over`). The other 219 are theorems or instances of
proposition-valued classes on both sides. Each of these is rejected if its two elaborated
statements differ. That was not checked: it needs both libraries built together at their
common pin (Lean 4.35.0, Mathlib `56a0058`), while the project's Lean service runs the
Library's pin, where only focused samples were compiled (Sections 5.6 and 7.2). Some differ
visibly in the source.

**Consequence.** Using both libraries in one module needs a fork of one of them that renames at
least the 113 certain clashes, in practice all 332 shared names, and every declaration that uses
them. The alternative is to keep each library in its own project and pass between them only
statements in the Library's and Mathlib's vocabulary. Upstreaming to Mathlib could remove some
clashes (137 of the FAG names are in `WeilConjectures/Mathlib`), but only after the declaration
is in Mathlib and both libraries have moved to that Mathlib and dropped their own copies. Neither
step is under the project's control.

## 9. Recommendation (item 7)

**Which library.** Use one sheaf library for both the cohomological branch and
Laumon's theorem. If FAG becomes the dependency for Laumon's theorem (plan
note, configuration B), take the premises from FAG too. The reasons:

1. The project's final theorem imports both branches, and one module cannot
   import the Stacks and FAG closures together (Section 8). Two sheaf libraries
   would require a fork of one of them that renames the shared declarations
   (332 names, at least 113 of which clash whatever their statements) and
   everything that depends on them. The alternative is to keep each library
   in its own project, but then the final theorem is not checked by one kernel
   in one environment.
2. FAG's premise closure costs almost nothing beyond Laumon's: 19 of its 7,275
   modules are outside the closure of the Laumon roots (Section 5.6). The
   Stacks premise closures add about 17,900 modules of an unreviewed tier.
3. FAG proves what the route needs: specialization over any base, proper and
   smooth base change, finiteness for proper morphisms, the limit theorem
   09YQ with the limit cones over finite subextensions, and the stalk formula
   03Q9 (Section 5.3). Its gaps are bridges that the Library would write in
   any case.

Stacks is the better source for the premises alone. It has a Galois-equivariant
`RΓ` whose action is already identified with the geometric one; 09YQ on the full
small étale sites, including the finite-stage descent of every cohomology class
over any algebraic extension, which gives a limit route through the Library's
own action without a separability hypothesis, together with the composition
rule for its cohomology maps; the change of coefficient universe for abelian
étale cohomology; descent of one locally constant sheaf to a stage (0GL2); and
the identification of the cohomology in its finiteness
theorem with ordinary cohomology for proper schemes (Sections 4.1–4.4). Its
coefficient ring is in `Type`, and part of it compiles on the Library's present pin. It is
the right choice only if FAG is not adopted for Laumon's theorem, or if a
renaming fork is accepted. On the Stacks route the remaining work is
bridges B1–B5: on the limit route, the comparison of the Library's module
cohomology with abelian `Sheaf.H` and its pullback compatibilities (B1), and the
identification of the Library's operator with Stacks' maps `etaleCohomologyMapTo`,
whose composition rule Stacks states (B2); for good reduction, the assembly of a
smooth proper model from the Library's own number-field spreading theorems, the
change to coefficients `ZMod e` with `e = Nat.card M` on an open where `e` is a
unit (`ZMod (p^{a_r})` on one open where `p` is a unit, for the Harris stages),
and the uniform extension of the Harris coefficients (B3, B3′); the inertia
transport (B4); and the coefficient transports for finiteness (B5). Stacks'
spreading-out theorem with no fixed relative dimension is then not needed. If the limit route is used, the import root
`Colimits/AlgebraicExtensionCohomologyColimit` adds 2 modules to the nine-root
closure (Section 7.1).

**Mode.** A dependency at a pinned commit: mode D under the plan note's
configuration B, with the Library on Mathlib `56a0058`. A port is not
appropriate. Only theorems cross the boundary, since every premise is stated
with the Library's own cohomology and actions (plan note, §5.2, criterion 1).
The closures are thousands of modules, and FAG at the Library's present pin
fails with at least 346 errors (Section 5.6). The audit rule for each theorem
used still applies: the comparison of statements, `#print axioms` on the built
roots (FAG's build hides `sorry` warnings), and the list of hypotheses each
carries.

**Which theorems (FAG).**

- `Etale.isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper`
  and `…_homology_lowerStar_of_smooth_of_isProper`, for good reduction and the
  Harris unramified statement, with coefficients `ULift (ZMod e)` on an open or
  strictly local base where `e` is a unit (F4).
- `Etale.isIso_baseChange_of_isProper` and `Etale.isIso_baseChange_of_smooth`,
  as auxiliaries.
- `Etale.isIso_homology_derivedBaseChangeMapPlus_of_isProper` and
  `isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper`, for
  finiteness.
- For smoothness (the general and Harris statements and, after the Library's
  reduction to one level (Section 2.4), the level-colimit statements), route
  (i) of F3: `Etale.cohomologyMap_isColimit_of_isLimit` (09YQ for `Sheaf.H`),
  with the cones `FiniteIntermediateField.isLimitSpecCone`,
  `FiniteIntermediateField.isLimitOverCone` and
  `Scheme.Hom.isLimitFiniteLevelCone`, and the composition rule
  `Etale.cohomologyPullbackFunctorial`. The `Ext` forms
  `Etale.exists_cohomologyRestrictOver_eq_of_isLimit` and
  `…_eq_zero_of_isLimit` are the alternative if the comparison F1 is made with
  `Ext`. Alternatively, for route (ii) of F3, the stalk
  formula `Etale.nonempty_geometricStalk_higherDirectImage_addEquiv` (03Q9)
  with its comparison map, the strict-henselization lemmas of
  `AlgebraicGeometry/Sites/StrictHenselizationField.lean`,
  `spec_map_strictHenselizationEval_comp_strictLocalizationToBase`,
  `Etale.cohomologyMap_bijective` (03SI),
  `Etale.bijective_mapExtComp_constantIntToRing` and
  `Scheme.etaleSheafEquivDiscreteContinuousRep` with its `ForgetIso` and `_ρ`.
- For the comparisons inside FAG (Section 5.2):
  `Etale.bijective_mapExtComp_constantIntToRing` and
  `forgetRightDerivedSectionsIso`.
- As inputs to F5: `bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap`
  applied to `Etale.isIso_globalSectionsUpperStarMap_upperStar_homology_of_smooth_of_isProper`,
  `Etale.galoisStalkMap_boundarySpecialization`,
  `Etale.injective_specializationStalk`,
  `Scheme.FiniteEtale.galoisToAut_hom_app_eq_of_mem_inertia`,
  `Scheme.exists_iso_uliftYoneda_of_isFiniteLocallyConstant`,
  `Scheme.exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing`,
  `Ideal.isStrictlyHenselianLocalRing_atPrime`, and the germ formulas
  `Scheme.toPresheafFiber_cospecializationMap` and
  `Etale.toPresheafFiber_specializationStalk` (Section 5.4).

The smooth proper model needs no external theorem. It is assembled from the
Library's `numberFieldSpreadSeparatedExistence`, `numberFieldSpreadEventualSmoothness`,
`numberFieldSpreadEventualProperness` and `numberFieldLevelModelBaseChange`, and
`numberFieldPrincipalLevelAbove` if a principal level is wanted (statements A.5,
bridge B3).

**Bridges to prove (Library side).**

- F1: coefficients and universes; change of ring to `Rcoeff/m^r Rcoeff` for
  finiteness, and to `ULift (ZMod e)` with `e = Nat.card M` (for Harris,
  `ULift (ZMod (p^{a_r}))`) for specialization, with comparisons natural and
  compatible with pullbacks.
- F2: the Library's actions, including the level operator `g_σ^♯`, against
  FAG's restriction maps.
- F3: either route (i), where FAG has the cone, 09YQ for `Sheaf.H` and the
  composition rule, and what remains is F1 with `Sheaf.H` as target, F2 for
  `Etale.cohomologyMap`, and the lift of the cone to a diagram over the base
  of the sheaf (Stacks' `galoisGlobalSections` and
  `isOpen_stabilizer_fieldBaseChangeGlobalSectionsGaloisAction` show the
  fixed-point argument); or route (ii), where what remains is the application
  of 03SI along the factorization of the field point, an exported bijectivity
  of 03Q9's comparison map, the compatibility of the `Ext`–`Sheaf.H`
  comparison with pullbacks, and the identification of the transported action
  with the geometric one.
- F4: the assembly of a smooth proper model of `X` over a ring of `T`-integers
  from the Library's spreading theorems (above), as
  `exists_numberFieldSmoothConnectedModel` does for geometrically connected
  models. For each finite `M`, FAG's specialization theorem is applied with
  `ULift (ZMod e)` coefficients on the base change of the model to the level
  `T ∪ numberFieldPrincipalExceptional K e`, or at the strict henselization at
  `v`; `S = T` does not depend on `M`. For Harris: one open `Spec 𝒪_F[1/pN]`,
  on which `p` and so every stage exponent `p^{a_r}` is a unit, with a smooth
  proper model of `X_U` on which every stage `A_r` extends to a locally
  constant constructible sheaf (B3′: the universal-abelian-scheme and
  monodromy argument of the Library's `HarrisCMCohomologyUnramified/Statement.md`).
  This uniform extension is the remaining mathematical obligation; the model
  of `X_U` itself is the Library assembly.
- F5: from the specialization isomorphism to `IsUnramifiedAt`. FAG proves
  over any base that the cospecialization map of `Rⁿf_*M` is bijective, and
  that the image of its specialization map `boundarySpecialization` is fixed
  by the global inertia group `Q.inertia`. It also gives the morphism
  `Spec B_Q ⟶ Y_(s)` through which both maps can be taken at the same points,
  and their germ formulas. What remains is the proof that the two maps agree
  at a geometric point over `v` (a uniqueness-of-lifts argument), the equivariant
  identification of the generic stalk with `Hⁿ(X_K̄, M)` (route (ii) of F3),
  and `Q.inertia` against the inertia of the completion.
- F6: `B_r` locally constant and constructible in FAG's sense.
- The derivation of the unramified statement from good reduction for smooth
  proper `X` (Section 6). For smoothness, route (ii) of F3 covers the geometric
  point of a separable closure `Ks` (FAG's `etaleSheafEquivDiscreteContinuousRep`
  is for `Gal(Ks/K)`), and the Library's `AlgebraicClosure K` after the
  transport along `Aut(K̄/K) ≅ Gal(Ks/K)` and 03SI. It does not cover an
  arbitrary algebraic `L/K`, separable or not. `GaloisCohomologySmoothStatement`
  for such `L` needs the finite-subextension limit route (i), which works for
  every algebraic extension.

Generic base change over an open of `Spec 𝒪_K` is left as a premise without a
source. FAG's two forms over a field (Section 5.3) do not apply to it, and
whether FAG's proofs extend to a mixed-characteristic base was not examined. If the
premise is kept, it needs its own proof.

## 10. Attribution and evidence limits

- The Stacks statements and their line numbers were checked in a clone at
  `c496df0`, the Library statements in Library `fcb85a7e`, and the FAG
  statements at `a25955c`. Every statement in `statements.md` was copied
  mechanically from the registered copies of both libraries and from the
  Library, by line range, and the fully qualified names were checked against
  the `namespace` lines in scope.
- The reduction of the level-colimit statements to single levels (Section 2.4)
  and the uniform extension of the Harris coefficients (B3′, F4) are read from
  the Library's Lean statements and its `Statement.md`, not proved here.
- Sections C.5–C.7 of
  `statements.md` were made by the same method, generating the blocks by line
  range with a script from the clone at `a25955c`, and the Stacks inertia names
  in B4 were taken from the clone at `c496df0`. The FAG claims of Sections 5.3–5.6 they support are
  read from these statements and from module documentation. None of the cited
  modules was compiled.
- The absence statements of Section 5.3 (no Galois-equivariant `RΓ` and no
  Galois action on `Hⁿ(X_Ω, F)` for every `n` in FAG) rest on text searches:
  of the files that mention `Gal(` or `≃ₐ[`, and of the uses of
  `geometricFiberGaloisMap`. A construction under other names could have been
  missed.
- Sections C.8–C.9 of `statements.md` were made
  by the same method, and the FAG checkout was searched for the files that mention
  the generic base-change properties (Section 5.3). Every closure, scan and
  shared-name list was made with the corrected import parser
  (Sections 5.6, 7.1 and 8), and the main figures were recounted
  independently, with the same results. The description of route (ii) of F3
  is read from the statements and the proof outline of
  `StalkFormula.lean`; the route was not attempted.
- Sections B.7–B.8 and C.10–C.11 of
  `statements.md` were made by the same method, from the copies at `c496df0` and
  `a25955c`, and the closures of the roots they cite were computed with the same
  script (Sections 4.2 and 5.6); the FAG figures were recounted. The
  descriptions of route (i) of F3, of the field case of route (ii) and of the
  comparison in F5 are read from these statements and from the proofs that
  combine them (`FieldExtension.lean:155-176`,
  `FieldCohomologicalDimension.lean:114-127`,
  `SmoothProperLocallyConstant.lean:241-247`); none of the remaining steps was
  attempted.
- Sections B.9–B.11 and C.12 of
  `statements.md` were made by the same method, and the closures of the roots
  they cite were computed with the same script (Sections 5.6 and 7.1). The limit
  route of Section 4.2, the arithmetic localization first considered for B3 (now
  replaced by the Library's own theorems), the remaining parts of B1
  and the comparison of the two specialization maps in F5 are read from these
  statements and from the proofs that use them
  (`SmoothProperHigherDirectImageLocallyConstantReduction.lean:265-295`,
  `:474-507`; `StructureSheafComparison.lean:295-307`); none of them was
  attempted. Whether Stacks' 03FD comparison applies to Mathlib's small étale
  site was not checked.
- Sections A.5 (from the Library at
  `f050c0b1`) and B.12 of `statements.md` were made by the same method. The assembly of
  the smooth proper model in B3 and F4 is read from the Library's statements
  and from the proof of `exists_numberFieldSmoothConnectedModel`
  (`NumberFieldAlmostAllLocalPoints.lean:42-109`). The change of coefficients
  and base for specialization is read from the hypotheses of 0GLI, 0GKD and
  FAG's `SmoothProperLocallyConstant.lean:153-189`, and the stage exponents of
  the Harris coefficients from step 1 of the Library's
  `HarrisCMCohomologyUnramified/Statement.md`. Neither the assembly nor the
  comparison of the `R`-module cohomology with the `ZMod e`-module cohomology
  was attempted. The unit property of `e` on the enlarged level is argued from
  `numberFieldPrincipalSIntegerEquiv`; the Library does not state it.
- The closures are textual import closures and the scans are text scans. No
  `#print axioms` was run on any premise root of either library.
- The shared names of Section 8 were read from source text. Lean's rule for
  duplicate imports was checked on small test modules, not on the two
  libraries. Whether the 219 theorem-like shared names have identical
  statements was not checked.
- The compiles cover 318 Stacks modules and 467 FAG modules, which failed. No
  premise theorem of either library was compiled.
- The bridges are estimates of what remains, read from statements. None was
  attempted.
- The claim that the final theorem must import both branches follows the plan
  note (§5.2, criterion 5). The configuration is not chosen here.
