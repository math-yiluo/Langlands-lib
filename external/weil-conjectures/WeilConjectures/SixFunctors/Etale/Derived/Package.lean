/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethVerdier
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteStage
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived

/-!

# The six-operations package

This file states the summary theorem of the block: the six operations
`Lf^*`, `Rf_*`, `Rf_!`, `Rf^!`, `- ⊗ᴸ -` and `RHom(-, -)` exist on the ambient derived
categories of étale sheaves, descend to the small categories `Dᵇc` and `Dctf`, and satisfy the
eight clauses of the blueprint: adjunctions, base change, the projection formula,
compactification-independence and proper coincidence, the orientation, duality, the relative
product, and stability of the small categories.

## Main definitions

- `AlgebraicGeometry.Etale.SixOperationsPackage` (`sk-thm-sf-package`): the eight clauses,
  one named field each.

## Main statements

- `AlgebraicGeometry.Etale.sixOperationsPackage` (`sk-thm-sf-package`): the eight clauses
  hold.

## Implementation notes

The package is stated in the setting of `definition-constructible-sheaves--6`: the coefficients are
`ModuleCat Λ` for a finite ring `Λ` (with a normalized Tate twist datum, for the orientation
clause) whose exponent is invertible on the base field `k`, and `Y` is separated of finite
type over `k`. For a general coefficient category the clauses are false: for `Λ = 𝔽_p` over
`𝔽̄_p`, `Rf_*` of the constant sheaf along `𝔸¹ ⟶ Spec 𝔽̄_p` is not constructible
(Artin–Schreier).

Each clause is one of the statements of this directory, and `sixOperationsPackage` is the
assembly: the clauses are proved from the corresponding statements. Smooth base change for `Rf_*`
is stated, as in the blueprint, on the bounded below derived categories `D⁺`, where it is the
smooth base change theorem of the smooth base change chapter; the comparison of the `D⁺` base
change map with the unbounded `AlgebraicGeometry.Etale.derivedBaseChangeMap` is not available.

The clauses of the blueprint that this statement does not carry are the ones whose content is
an identity *between canonical comparison transformations* rather than the existence of an
isomorphism: the naturality clauses, and the compatibilities with finite reduction, scalar
extension and the pro-étale realization, which would need a change-of-coefficients functor
between stages; see the module docstring of
`WeilConjectures.SixFunctors.Etale.Derived.Stability`.

Three further components of the blueprint's duality clause (6) are not collected here, since
they need data that the package's `f` does not carry: `𝔻_X K ≅ K^∨(d)[2d]` for perfect `K`
needs an orientation and is
`AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual`, and global
duality and the derived Poincaré pairing need `X` smooth proper geometrically connected and
are the two statements of `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality`.

## Expository remarks of the package

The following remarks of the blueprint subsection `sk-thm-sf-package` are pointers or scope
statements and carry no mathematical content beyond the results they cite:

- `rem-sf-yoga` (the dictionary from the axioms of the six-functor datum to the classical duality
  statements) and `rem-sf-axiom-verification` (each axiom is supplied by the corresponding result
  of this directory): this is the assembly `sixOperationsPackage` itself.
- `rem-sf-ctf-descent`, `proposition-six-operations-change-coefficients`,
  `lemma-change-coefficients-exceptional-inverse-image` and
  `theorem-exceptional-inverse-image`: the coefficient comparisons of the exceptional
  adjoint are
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual_and_reductionModIdeal`
  (`lemma-change-coefficients-exceptional-inverse-image--1`) and
  `AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`.
- `theorem-verdier-biduality`, `rem-weil-biduality-boundary-status` and `open-sf-preservation-gaps`:
  finite-stage biduality is `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`, its
  Weil-equivariant form is `AlgebraicGeometry.Etale.WeilComplex.isIso_verdierDualDoubleDual`, and
  the `ℚ̄_ℓ` stage is `AlgebraicGeometry.ProEtale.CondensedRing.isIso_verdierBiduality`
  (`theorem-verdier-biduality`).

The reconstruction of normalized towers, an ingredient of the finite-level comparison, is
`AlgebraicGeometry.Etale.NormalizedTower.isDerivedBaseChange_of_isHomotopyLimit`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] (k : Type u) [Field k]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k)) [HasCompactification f]
  [QuasiCompact f] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
  [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- Blueprint `sk-thm-sf-package`: The six-operations package.

Let `k` be a field, `Λ` a finite ring with a Tate twist datum, `Y` separated of finite type over
`k` with structure morphism `a_Y`, and `f : X ⟶ Y` separated of finite type, with
`a_X = f ≫ a_Y`. The twist `Λ_X(d)` of the orientation clause is that of the ambient Tate twist
datum; the clause is only true for a normalized datum
(`AlgebraicGeometry.Etale.HasTateTwist.IsNormalized`), which `sixOperationsPackage` assumes.
The eight clauses of the blueprint, one group of fields each:
1. **Adjunctions.** `Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!`.
2. **Base change.** For a Cartesian square
   ```
     X' --g'--> X
     |          |
     f'         f
     v          v
     Y' --g---> Y
   ```
   one has `Lg^* Rf_! ≅ Rf'_! Lg'^*`; and `Lg^* Rf_* ≅ Rf'_* Lg'^*` for proper `f`, and for
   smooth `g` on `D⁺`, where the base change map `g^* Rf_* ⟶ Rf'_* g'^*` is an isomorphism.
3. **Projection formula.** `Rf_!(K ⊗ᴸ Lf^* L) ≅ Rf_! K ⊗ᴸ L` at every `K` and `L`.
4. **Compactifications and proper coincidence.** `Rf_!` is independent of the compactification,
   `R(f ≫ h)_! ≅ Rh_! Rf_!`, and `Rf_! ≅ Rf_*` for proper `f`.
5. **Orientation.** A smooth `f` of pure relative dimension `d` carries an orientation
   `Rf^! Λ_Y ≅ Lf^* Λ_Y ⊗ Λ_X(d)[2d]`.
6. **Duality.** `𝔻_X 𝔻_X ≅ id` on `Dctf(X, Λ)`, and the Verdier exchange
   `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`.
7. **Relative product.** The four Künneth comparisons over `k` are isomorphisms.
8. **Stability.** `Lf^*`, `- ⊗ᴸ -`, `Rf_*`, `Rf_!`, `Rf^!` and `𝔻_X` carry `Dctf` into
   `Dctf`.
See the module docstring for the clauses that are deliberately not carried here.

Blueprint `def-sf-datum`: Six-functor datum, axiomatized

The axioms (A1)–(A4) and (A6) of a six-functor datum, at a finite coefficient stage
`Λ = A_{E,n}` on the étale sites: the fields of this structure are the adjunctions (A1), the base
change isomorphisms (A2), the projection formula (A3), the composition law and proper
coincidence (A4) and Verdier biduality (A6); the compatibilities (A5) with change of coefficients
are not carried (see the module docstring).

Blueprint `rem-sf-summary`: What a six-functor formalism is

The six-functor formalism summarised by the remark is the conjunction of the clauses of this
structure: the two adjoint pairs, base change, the projection formula, and proper coincidence
together with the orientation of a smooth morphism. -/
structure SixOperationsPackage : Prop where
  /-- (1) The adjunction `Lf^* ⊣ Rf_*`. -/
  upperStarLowerStarAdjunction :
    Nonempty (L((f)^*[ModuleCat.{u + 1} Λ]) ⊣ R((f)_*[ModuleCat.{u + 1} Λ]))
  /-- (1) The adjunction `Rf_! ⊣ Rf^!`. -/
  lowerShriekUpperShriekAdjunction :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⊣ R(f)^![Λ])
  /-- (2) Base change for `Rf_!`. -/
  baseChangeLowerShriek : ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
    IsPullback g' f' f g → ∀ [HasCompactification f'],
      Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ])
  /-- (2) Proper base change for `Rf_*`. -/
  baseChangeLowerStarOfProper :
    ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback g' f' f g → IsProper f →
      Nonempty (R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R((f')_*[ModuleCat.{u + 1} Λ]))
  /-- (2) Smooth base change for `Rf_*`: for smooth `g` the base change map
  `g^* Rf_* ⟶ Rf'_* g'^*` is an isomorphism of functors `D⁺(X_ét, Λ) ⥤ D⁺(Y'_ét, Λ)`. -/
  baseChangeLowerStarOfSmooth :
    ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), Smooth g →
      IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq)
  /-- (3) The projection formula. -/
  projectionFormula : ∀ K L, HasProjectionFormula (ModuleCat.{u + 1} Λ) f K L
  /-- (4) `Rf_!` is independent of the chosen compactification. -/
  lowerShriekCompactificationIndependent : ∀ c c' : Compactification f,
    Nonempty (Rf_!(c)[ModuleCat.{u + 1} Λ] ≅ Rf_!(c')[ModuleCat.{u + 1} Λ])
  /-- (4) The composition law `R(f ≫ h)_! ≅ Rf_! ⋙ Rh_!`. -/
  lowerShriekComp : ∀ {Z : Scheme.{u}} (h : Y ⟶ Z) [HasCompactification h]
    [HasCompactification (f ≫ h)] [QuasiCompact (f ≫ h)],
    Nonempty (R(f ≫ h)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(h)_![ModuleCat.{u + 1} Λ])
  /-- (4) Proper coincidence `Rf_! ≅ Rf_*`. -/
  lowerShriekIsoLowerStarOfProper :
    IsProper f → Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ≅ R((f)_*[ModuleCat.{u + 1} Λ]))
  /-- (5) A smooth morphism of pure relative dimension carries an orientation. -/
  orientation : ∀ d : ℕ, SmoothOfRelativeDimension d f → Nonempty (Orientation Λ f d)
  /-- (6) Verdier biduality on `Dctf(X, Λ)`. -/
  biduality : ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
    Nonempty (K ≅ (verdierDual Λ (f ≫ aY)).obj
      (op ((verdierDual Λ (f ≫ aY)).obj (op K))))
  /-- (6) The Verdier exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X`. -/
  verdierExchange : ∀ M,
    Nonempty ((verdierDual Λ aY).obj
        (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((verdierDual Λ (f ≫ aY)).obj (op M)))
  /-- (7) The four Künneth comparisons over `k` are isomorphisms. -/
  kunneth : HasKunnethComparisons Λ (Spec (.of k))
  /-- (8) `Lf^*` carries `Dctf` into `Dctf`. -/
  ctfLeftDerivedUpperStar : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)
  /-- (8) `- ⊗ᴸ -` carries `Dctf` into `Dctf`. -/
  ctfTensor : ∀ K M, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M)
  /-- (8) `Rf_*` carries `Dctf` into `Dctf`. -/
  ctfRightDerivedLowerStar : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)
  /-- (8) `Rf_!` carries `Dctf` into `Dctf`. -/
  ctfRightDerivedLowerShriek : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)
  /-- (8) `Rf^!` carries `Dctf` into `Dctf`. -/
  ctfRightDerivedUpperShriek : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((R(f)^![Λ]).obj K)
  /-- (8) `𝔻_X` carries `Dctf` into `Dctf`. -/
  ctfVerdierDual : ∀ K,
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
        ((verdierDual Λ (f ≫ aY)).obj (op K))

/-- Blueprint `sk-thm-sf-package`: The six-operations package.

The eight clauses of `AlgebraicGeometry.Etale.SixOperationsPackage` hold for a finite `Λ` whose
exponent is invertible on `k`, for `k` algebraically closed as in the blueprint (Verdier
biduality is proved over algebraically closed fields). Every clause is one of the propositions of
this directory, and the proof is the assembly: smooth base change is
`AlgebraicGeometry.Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder`,
every sheaf of `Λ`-modules being torsion of order invertible on `Y`, and the orientation is
smooth purity (`AlgebraicGeometry.Etale.Orientation.nonempty`). The Tate twist datum is assumed
normalized: for the untwisted datum `Λ_X(m) = Λ_X` the orientation clause fails over `ℚ`,
where `Rf^! Λ ≅ μ_n[2] ≇ Λ[2]` for `𝔸¹_ℚ ⟶ Spec ℚ`. -/
theorem sixOperationsPackage [IsAlgClosed k] [HasTateTwist.IsNormalized Λ]
    [HasInvertibleExponent Λ (Spec (.of k))] [IsSeparated f] :
    SixOperationsPackage Λ k f aY where
  upperStarLowerStarAdjunction := ⟨derivedUpperStarLowerStarAdjunction _ f⟩
  lowerShriekUpperShriekAdjunction := ⟨rightDerivedUpperShriekAdjunction _ f⟩
  baseChangeLowerShriek _ _ f' sq _ :=
    have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
    ⟨asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)⟩
  baseChangeLowerStarOfProper _ _ _ sq _ :=
    have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
    ⟨asIso (derivedBaseChangeMap _ sq.toCommSq)⟩
  baseChangeLowerStarOfSmooth g _ _ sq hg := by
    have := hg
    have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom aY
    obtain ⟨N, hN₀, hN, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
    have (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
        IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := by
      have h₀ := Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ g sq K
        fun _ ↦ IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ N hN₀.ne' hN hNY _
      -- `h₀` is stated with the Mathlib instance `IsGrothendieckAbelian (ModuleCat Λ)`, the goal
      -- with the shortcut `ModuleCat.isGrothendieckAbelian_of_commRing`; comparing them directly
      -- is a kernel deterministic timeout, so the instance is generalized first.
      revert h₀
      generalize ModuleCat.isGrothendieckAbelian_of_commRing Λ = i
      intro h₀
      exact (Subsingleton.elim _ i) ▸ h₀
    exact NatIso.isIso_of_isIso_app _
  projectionFormula K L := hasProjectionFormula_of_finite Λ f K L
  lowerShriekCompactificationIndependent c c' :=
    ⟨rightDerivedLowerShriekOfCompactificationIso Λ c c'⟩
  lowerShriekComp h := nonempty_iso_rightDerivedLowerShriek_comp Λ f h
  lowerShriekIsoLowerStarOfProper _ :=
    nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar _ f
  orientation _ hd :=
    have := hd
    have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom (f ≫ aY)
    Orientation.nonempty (Λ := Λ) f aY
  biduality _ hK := nonempty_iso_verdierDual_verdierDual Λ (f ≫ aY) hK
  verdierExchange M := nonempty_iso_verdierDual_rightDerivedLowerShriek Λ f aY M
  kunneth := hasKunnethComparisons Λ k
  ctfLeftDerivedUpperStar _ hK := constructibleFiniteTor_leftDerivedUpperStar _ f hK
  ctfTensor _ _ hK hM := constructibleFiniteTor_tensor _ X hK hM
  ctfRightDerivedLowerStar _ hK :=
    have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom aY
    constructibleFiniteTor_rightDerivedLowerStar Λ (f ≫ aY) aY f rfl hK
  ctfRightDerivedLowerShriek _ hK :=
    have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom aY
    constructibleFiniteTor_rightDerivedLowerShriek Λ aY f hK
  ctfRightDerivedUpperShriek _ hK :=
    have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom aY
    constructibleFiniteTor_rightDerivedUpperShriek Λ aY f hK
  ctfVerdierDual _ hK := constructibleFiniteTor_verdierDual Λ (f ≫ aY) hK

omit [HasTateTwist Λ] in
/-- Blueprint `prop-functor-package`, clause (3): **compactly supported direct image of the
localization triangle.** For a quasi-compact open immersion `j : U ⟶ X` with closed complement
`i : Z ⟶ X`, a morphism `f : X ⟶ Y` and finite coefficients, applying `Rf_!` to the open–closed
triangle `j_! j^* K ⟶ K ⟶ i_* i^* K ⟶` (`AlgebraicGeometry.Etale.exists_distTriang_openClosed`)
and the composition law (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`)
gives a distinguished triangle `R(j ≫ f)_! j^* K ⟶ Rf_! K ⟶ R(i ≫ f)_! i^* K ⟶`. -/
theorem exists_distTriang_rightDerivedLowerShriek_openClosed {U Z X Y : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification j] [HasCompactification i] [HasCompactification (j ≫ f)]
    [HasCompactification (i ≫ f)] (K : DerivedCategoryModule Λ X) :
    ∃ T ∈ distTriang (DerivedCategoryModule Λ Y),
      Nonempty (T.obj₁ ≅ (R(j ≫ f)_![ModuleCat.{u + 1} Λ]).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      Nonempty (T.obj₂ ≅ (R(f)_![ModuleCat.{u + 1} Λ]).obj K) ∧
      Nonempty (T.obj₃ ≅ (R(i ≫ f)_![ModuleCat.{u + 1} Λ]).obj
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j i hij K
  obtain ⟨cj⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ j f
  obtain ⟨ci⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ i f
  let F := R(f)_![ModuleCat.{u + 1} Λ]
  let ej : D((j)_!open[ModuleCat.{u + 1} Λ]) ≅ R(j)_![ModuleCat.{u + 1} Λ] :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarIdIso Λ X).symm ≪≫
      rightDerivedLowerShriekIso Λ (Compactification.ofIsOpenImmersion j)
  refine ⟨F.mapTriangle.obj _, F.map_distinguished _ hw, ⟨?_⟩, ⟨Iso.refl _⟩, ⟨?_⟩⟩
  · exact F.mapIso (ej.app _ ≪≫ (R(j)_![ModuleCat.{u + 1} Λ]).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ j).app K).symm) ≪≫ (cj.app _).symm
  · exact F.mapIso ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ i).symm.app _ ≪≫
      (R(i)_![ModuleCat.{u + 1} Λ]).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory _ i).app K).symm) ≪≫ (ci.app _).symm

/-- Blueprint `prop-functor-package`: **the coefficient and functor package on the proved
domains**, at the finite stages `Λ = A_{E,n}`.

For `k` algebraically closed, a finite ring `Λ` with a normalized Tate twist datum whose exponent is
invertible on `k`, and a separated finite-type morphism `f : X ⟶ Y` of separated finite-type
`k`-schemes:

* the clauses of the six-operations package hold (`AlgebraicGeometry.Etale.SixOperationsPackage`):
  compactification independence and the composition law of `Rf_!` and `Rf_! ≅ Rf_*` for proper
  `f` (clauses (2) and (3)), base change (clause (4)), the projection formula (clause (5)), smooth
  purity (clause (6)), biduality and the Verdier exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X` on `Dctf`
  (clause (7));
* applying `Rf_!` to the localization triangle of a quasi-compact open immersion and its closed
  complement gives a distinguished triangle (clause (3),
  `AlgebraicGeometry.Etale.exists_distTriang_rightDerivedLowerShriek_openClosed`);
* on `Dctf(Y, Λ)` the exceptional inverse image is `Rf^! = 𝔻_X Lf^* 𝔻_Y` (clause (7),
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar`).

The integral reduction compatibilities of clause (2) are
`AlgebraicGeometry.Etale.functorPackage_integral`. Clause (1) (finite coefficient-field extension
and descent to `ℚ̄_ℓ`) and the integral and field stages of clause (7) are not part of this
statement; for strict Weil complexes over a finite field, clauses (2)–(4) are the statements of
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`. -/
theorem functorPackage [IsAlgClosed k] [HasTateTwist.IsNormalized Λ]
    [HasInvertibleExponent Λ (Spec (.of k))] [IsSeparated f] :
    SixOperationsPackage Λ k f aY ∧
    (∀ {U Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (i : Z ⟶ X)
      [IsClosedImmersion i], Set.range i.base = (Set.range j.base)ᶜ →
      ∀ [HasCompactification j] [HasCompactification i] [HasCompactification (j ≫ f)]
        [HasCompactification (i ≫ f)] (K : DerivedCategoryModule Λ X),
        ∃ T ∈ distTriang (DerivedCategoryModule Λ Y),
          Nonempty (T.obj₁ ≅ (R(j ≫ f)_![ModuleCat.{u + 1} Λ]).obj
            ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
          Nonempty (T.obj₂ ≅ (R(f)_![ModuleCat.{u + 1} Λ]).obj K) ∧
          Nonempty (T.obj₃ ≅ (R(i ≫ f)_![ModuleCat.{u + 1} Λ]).obj
            ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))) ∧
    ∀ L, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L →
      Nonempty ((R(f)^![Λ]).obj L ≅
        (verdierDual Λ (f ≫ aY)).obj
          (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
            ((verdierDual Λ aY).obj (op L))))) :=
  ⟨sixOperationsPackage Λ k f aY,
    fun j _ _ i _ hij _ _ _ _ K ↦
      exists_distTriang_rightDerivedLowerShriek_openClosed Λ j i hij f K,
    fun _ hL ↦
      nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ (f ≫ aY) aY f rfl hL⟩

end Etale

end AlgebraicGeometry
