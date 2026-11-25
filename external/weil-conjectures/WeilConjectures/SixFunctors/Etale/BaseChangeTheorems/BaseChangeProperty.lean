/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange

/-!

# The base change property for torsion coefficients, and injective acyclicity

Fix a commutative ring `Λ` and a morphism of schemes `f : X ⟶ Y`. This file isolates two
properties of `f`, both quantified over *all* base changes of `f`, which the proof of the
proper base change theorem proceeds by:

- `AlgebraicGeometry.Etale.HasTorsionBaseChange`, the property `PBC(f)`: the derived base
  change map `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` is an isomorphism at every
  object of `D⁺(X_ét, Λ)` with torsion cohomology;
- `AlgebraicGeometry.Etale.HasInjectiveAcyclicity`, the property `IA(f)`: for every
  injective *torsion* sheaf `I` on `X_ét`, the base change `g'^{-1} I` has no higher direct
  images along `f'`.

The two are equivalent for proper `f` and torsion coefficients
(`AlgebraicGeometry.Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity`), and the proof
of proper base change is carried out on the `IA` side, where the statement is a vanishing
statement about a single sheaf rather than a statement about a complex: `IA` composes,
cancels along proper surjections, and can be checked on geometric stalks.

`PBC` for proper `f` is *stated*, not proved, in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`; the content of this file and
of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` is the road leading
there, and `Proper` derives its theorem from them.

## Relation to `Etale.IsBaseChangeIso`

`AlgebraicGeometry.Etale.IsBaseChangeIso` of
`WeilConjectures.SixFunctors.BaseChange.Derived` already asks that the same derived base
change map be an isomorphism, for a general coefficient category and with *no* torsion
hypothesis. That is the right formulation for a finite morphism, where base change holds
unrestrictedly (`AlgebraicGeometry.Etale.isBaseChangeIso_of_isFinite`), but it is false for
a proper morphism and non-torsion coefficients, which is why the property used here carries
the restriction to objects with torsion cohomology. The two are compared by
`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isBaseChangeIso` and, when `Λ` is torsion
as an additive group, `AlgebraicGeometry.Etale.isBaseChangeIso_of_hasTorsionBaseChange`.

## Coefficient rings

The blueprint states `IA` for injective sheaves of `𝐅_r`-modules and one prime `r` at a
time, and reaches a general torsion coefficient ring by dévissage: `𝐅_r`-modules, then
`n`-torsion sheaves by induction on the number of prime factors of `n`, then all torsion
sheaves as a filtered colimit. The sheaf-level dévissage is
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage`, and the passage from the
rings `Λ ⧸ pΛ` to `Λ` is in `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients`.
The equivalence below is stated for a coefficient ring `Λ` which is torsion as an additive
group — the case `Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism — where every sheaf of
`Λ`-modules is torsion and no dévissage is needed.

## Proof of the equivalence

`PBC ⇒ IA` (`AlgebraicGeometry.Etale.HasTorsionBaseChange.hasInjectiveAcyclicity`) applies the
base change property to an injective sheaf placed in degree `0`. For `IA ⇒ PBC`
(`AlgebraicGeometry.Etale.HasInjectiveAcyclicity.hasTorsionBaseChange`) one represents an
object of `D⁺` by a bounded below complex `I` of injectives. The derived base change map at `I`
is the termwise underived base change map `g^* f_* I ⟶ f'_* g'^* I`, an isomorphism for proper
`f` (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper`), followed by the unit
`f'_* g'^* I ⟶ Rf'_*(g'^* I)`, an isomorphism because the terms of `g'^* I` are
`f'_*`-acyclic by `IA`
(`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`).

## Main definitions

- `AlgebraicGeometry.Etale.HasTorsionBaseChange`: the property `PBC(f)`.
- `AlgebraicGeometry.Etale.HasInjectiveAcyclicity`: the property `IA(f)`.
- `AlgebraicGeometry.Etale.HasPrimeInjectiveAcyclicity`: the case `Λ = 𝐅_r` of `IA(f)`.
- `AlgebraicGeometry.Etale.HasAllPrimeInjectiveAcyclicity`: `IA_r(f)` for every prime `r`.

## Main statements

- `AlgebraicGeometry.Etale.HasTorsionBaseChange.hasInjectiveAcyclicity`: `PBC(f) ⇒ IA(f)`.
- `AlgebraicGeometry.Etale.HasInjectiveAcyclicity.hasTorsionBaseChange`: `IA(f) ⇒ PBC(f)` for a
  proper morphism `f` and a torsion coefficient ring.
- `AlgebraicGeometry.Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity`:
  `PBC(f) ↔ IA(f)` for a proper morphism `f` and a torsion coefficient ring.

## References

- Stacks Project, Lemma 59.91.6, the equivalence of the two properties,
  <https://stacks.math.columbia.edu/tag/0A4B>
- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>
- [SGA 4, Exp. XII, Théorème 5.1]

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y : Scheme.{u}}

/-- **The base change property** `PBC(f)` of a morphism of schemes `f : X ⟶ Y`, for torsion
coefficients: for every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and every object `K` of `D⁺(X_ét, Λ)` whose cohomology sheaves are all torsion, the derived
base change map `BC_sq(K) : g^*(Rf_* K) ⟶ Rf'_*(g'^* K)` is an isomorphism. No hypothesis is
imposed on `g`, and none on `f`: the proper base change theorem says that `PBC(f)` holds
whenever `f` is proper.

This is the restriction to torsion cohomology of `AlgebraicGeometry.Etale.IsBaseChangeIso`,
which is the declaration realising the blueprint's `definition-torsion-pbc-property--1`; see the
module docstring. (blueprint: `sec-Torsion-sheaves-and-acyclicity`) -/
def Etale.HasTorsionBaseChange (f : X ⟶ Y) : Prop :=
  ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄ (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
    Etale.DerivedCategory.Plus.moduleTorsionHomology Λ X K →
      IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)

/-- A morphism for which the derived base change map is an isomorphism on all of `D⁺`
satisfies the base change property for torsion coefficients. For a finite morphism the
hypothesis holds by `AlgebraicGeometry.Etale.isBaseChangeIso_of_isFinite`. -/
theorem Etale.hasTorsionBaseChange_of_isBaseChangeIso (f : X ⟶ Y)
    [Etale.IsBaseChangeIso (ModuleCat.{u + 1} Λ) f] :
    Etale.HasTorsionBaseChange Λ f :=
  fun _ _ _ _ _ sq K _ ↦
    have : IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
      Etale.IsBaseChangeIso.isIso _ _ _ sq
    NatIso.isIso_app_of_isIso _ K

/-- If the coefficient ring `Λ` is torsion as an additive group, the torsion hypothesis in
`AlgebraicGeometry.Etale.HasTorsionBaseChange` is vacuous and the property is exactly
`AlgebraicGeometry.Etale.IsBaseChangeIso`. -/
theorem Etale.isBaseChangeIso_of_hasTorsionBaseChange (hΛ : IsAddTorsion Λ) {f : X ⟶ Y}
    (hf : Etale.HasTorsionBaseChange Λ f) :
    Etale.IsBaseChangeIso (ModuleCat.{u + 1} Λ) f where
  isIso _ _ _ sq :=
    have : ∀ K, IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
      fun K ↦ hf sq K (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X hΛ K)
    NatIso.isIso_of_isIso_app _

/-- **Injective acyclicity** `IA(f)` of a morphism of schemes `f : X ⟶ Y`: for every
cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and every *injective torsion* sheaf `I` of `Λ`-modules on `X_ét`, the higher direct images
of its pullback vanish: `Rᵠf'_*(g'^{-1} I) = 0` for `q > 0`. Here `Rᵠf'_* G` is the `q`-th
cohomology sheaf of `Rf'_*` applied to `G` placed in degree `0`.

The restriction to torsion `I` is what makes `PBC(f) ⇒ IA(f)` correct over a coefficient
ring which is not itself torsion: `PBC(f)` constrains only objects with torsion cohomology.
For a torsion `Λ` — the case in which the two properties are compared below — every sheaf of
`Λ`-modules is torsion and the restriction is vacuous.

This is the form in which the proper base change theorem is actually proved: it is a
vanishing statement about a single sheaf, it composes, it cancels along proper surjections,
and it can be checked on geometric stalks.
(blueprint: `definition-injective-acyclicity--1`; the property `IA_r(f)`
of the latter is the case `Λ = 𝐅_r`, where every sheaf is torsion) -/
def Etale.HasInjectiveAcyclicity (f : X ⟶ Y) : Prop :=
  ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄ (_sq : IsPullback g' f' f g)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)), IsTorsionModuleSheaf I → Injective I →
      ∀ q : ℤ, 0 < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
            (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
          (R+((f')_*[ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
                ((g')^*[ModuleCat.{u + 1} Λ].obj I))))

/-- **Injective acyclicity with `𝐅_r`-coefficients** `IA_r(f)` of a morphism of schemes
`f : X ⟶ Y`: the property `AlgebraicGeometry.Etale.HasInjectiveAcyclicity` for the coefficient
ring `ZMod r`, lifted to the coefficient universe of the étale sheaf functors. For `r ≠ 0`
every sheaf of `ZMod r`-modules is torsion, so this says that the pullback of every injective
sheaf of `ZMod r`-modules along any base change of `f` has no higher direct images.
(blueprint: `definition-injective-acyclicity--1`) -/
def Etale.HasPrimeInjectiveAcyclicity (f : X ⟶ Y) (r : ℕ) : Prop :=
  Etale.HasInjectiveAcyclicity (ULift.{u + 1} (ZMod r)) f

/-- **Injective acyclicity for all primes** `IA(f)` of a morphism of schemes `f : X ⟶ Y`: the
property `IA_r(f)` (`AlgebraicGeometry.Etale.HasPrimeInjectiveAcyclicity`) holds for every
prime `r`. (blueprint: `definition-injective-acyclicity--1`) -/
def Etale.HasAllPrimeInjectiveAcyclicity (f : X ⟶ Y) : Prop :=
  ∀ r : ℕ, r.Prime → Etale.HasPrimeInjectiveAcyclicity f r

/-- **`PBC ⇒ IA`**: a morphism with the base change property for torsion coefficients has
injective acyclicity. For an injective torsion sheaf `I` on `X`, apply the base change property
to `I` placed in degree `0`: the source `g^*(Rf_* I[0]) ≅ g^*((f_* I)[0])` has no homology
outside degree `0` because `I` is injective, hence neither has the target
`Rf'_*(g'^* I[0]) ≅ Rf'_*((g'^* I)[0])`. No properness is needed.
(blueprint: `theorem-pbc-injective-acyclicity--1`) -/
theorem Etale.HasTorsionBaseChange.hasInjectiveAcyclicity (f : X ⟶ Y)
    (hf : Etale.HasTorsionBaseChange Λ f) : Etale.HasInjectiveAcyclicity Λ f := by
  intro Y' X' g f' g' sq I _ _ q hq
  let K := (DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).obj I
  have := hf sq K (Etale.DerivedCategory.Plus.moduleTorsionHomology_singleFunctor_obj Λ X I)
  have hsrc : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
        ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K))) :=
    IsZero.of_iso (Functor.map_isZero (g)^*[ModuleCat.{u + 1} Λ]
      ((f)_*[ModuleCat.{u + 1} Λ].isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor
        I hq.ne'))
      (((g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusHomologyFunctorIso q).app _).symm
  refine IsZero.of_iso (IsZero.of_iso hsrc ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K))).symm)
    ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
        ((((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app I))).symm

/-- Under injective acyclicity, the base change `g'^* I` of an injective torsion sheaf `I` is
`f'_*`-acyclic, in the sense of `CategoryTheory.Functor.rightAcyclic`. -/
lemma Etale.HasInjectiveAcyclicity.rightAcyclic {f : X ⟶ Y} (hf : Etale.HasInjectiveAcyclicity Λ f)
    {Y' X' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionModuleSheaf I] [Injective I] :
    (f')_*[ModuleCat.{u + 1} Λ].rightAcyclic ((g')^*[ModuleCat.{u + 1} Λ].obj I) := fun q ↦
  IsZero.of_iso (hf sq I inferInstance inferInstance (q + 1) (by lia))
    ((f')_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso
      ((g')^*[ModuleCat.{u + 1} Λ].obj I) (q + 1)).symm

/-- **`IA ⇒ PBC` given the underived exchange**: if `Λ` is torsion as an additive group, `f` has
injective acyclicity, and the underived base change map `g^* f_* ⟶ f'_* g'^*` is an isomorphism
for every cartesian square over `f`, then the derived base change map is an isomorphism on all
of `D⁺(X_ét, Λ)`. Represent `K` by a bounded below complex `I` of injectives. The derived base
change map at `I` is computed by the underived base change map `g^* f_* I ⟶ f'_* g'^* I`, a
termwise isomorphism by hypothesis, followed by the unit `f'_* g'^* I ⟶ Rf'_*(g'^* I)`, which is
an isomorphism because the terms of `g'^* I` are `f'_*`-acyclic by injective acyclicity
(`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`).
(blueprint: `theorem-pbc-injective-acyclicity--1`) -/
theorem Etale.HasInjectiveAcyclicity.hasTorsionBaseChange_of_isIso_baseChangeMap
    (hΛ : IsAddTorsion Λ) (f : X ⟶ Y)
    (hex : ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄
      (sq : IsPullback g' f' f g), IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq))
    (hf : Etale.HasInjectiveAcyclicity Λ f) : Etale.HasTorsionBaseChange Λ f := by
  intro Y' X' g f' g' sq K _
  have : IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := hex sq
  obtain ⟨n, hn⟩ := K.2
  have : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
  let P := (HomotopyCategory.Plus.quotient _).obj M
  suffices IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      (DerivedCategory.Plus.Qh.obj P)) by
    rw [← NatTrans.isIso_app_iff_of_iso _ e]
    exact this
  have hM : ∀ m, (f')_*[ModuleCat.{u + 1} Λ].rightAcyclic
      ((((g')^*[ModuleCat.{u + 1} Λ]).mapCochainComplexPlus.obj M).obj.X m) := fun m ↦
    have : Injective (M.obj.X m) := (L.obj.X m).2
    have : IsTorsionModuleSheaf (M.obj.X m) := .of_isTorsion hΛ _
    hf.rightAcyclic Λ sq (M.obj.X m)
  have h₁ : IsIso ((f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app
      (((g')^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.obj P)) :=
    (f')_*[ModuleCat.{u + 1} Λ].isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
      (((g')^*[ModuleCat.{u + 1} Λ]).mapCochainComplexPlus.obj M) hM
  have h₂ : IsIso ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P) := by
    dsimp only [P, M]
    infer_instance
  have hfac := Etale.derivedBaseChangeMapPlus_fac_app (ModuleCat.{u + 1} Λ) sq.toCommSq P
  have : IsIso (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P) ≫
      (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (DerivedCategory.Plus.Qh.obj P)) := by
    rw [hfac]
    infer_instance
  exact IsIso.of_isIso_comp_left (((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusUnith.app P)) _

/-- **`IA ⇒ PBC` for a proper morphism and a torsion coefficient ring**: if `Λ` is torsion as an
additive group and `f` is proper with injective acyclicity, then the derived base change map is
an isomorphism on all of `D⁺(X_ét, Λ)`. This is
`AlgebraicGeometry.Etale.HasInjectiveAcyclicity.hasTorsionBaseChange_of_isIso_baseChangeMap`, the
underived base change map being an isomorphism since `f` is proper
(`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper`).
(blueprint: `theorem-pbc-injective-acyclicity--1`) -/
theorem Etale.HasInjectiveAcyclicity.hasTorsionBaseChange (hΛ : IsAddTorsion Λ) (f : X ⟶ Y)
    [IsProper f] (hf : Etale.HasInjectiveAcyclicity Λ f) : Etale.HasTorsionBaseChange Λ f :=
  hf.hasTorsionBaseChange_of_isIso_baseChangeMap Λ hΛ f fun _ _ _ _ _ sq ↦
    Etale.isIso_baseChangeMap_of_isProper Λ sq

/-- **The base change property is injective acyclicity**: for a proper morphism `f : X ⟶ Y`
and a coefficient ring `Λ` which is torsion as an additive group, the two properties of the
preceding definitions agree. That is, for every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

the derived base change map is an isomorphism on every bounded below complex if and only if
`Rᵠf'_*(g'^{-1} I) = 0` for `q > 0` and every injective sheaf `I` on `X_ét`.

For `PBC ⇒ IA`, apply `PBC` to the complex `I[0]` concentrated in degree `0`: its source
`g^*(Rf_* I[0]) = g^*(f_* I)[0]` is again concentrated in degree `0` because `I` is
injective, hence so is the target `Rf'_*(g'^{-1} I)`, which is the required vanishing. The
converse resolves a torsion sheaf by injectives, uses `IA` to see that the resolution stays
`f'_*`-acyclic after base change, and compares the two complexes termwise by the underived
exchange morphism, which is an isomorphism because at a geometric point of `Y'` both sides
are sections over the same proper geometric fibre.
(blueprint: `theorem-pbc-injective-acyclicity`, `theorem-pbc-injective-acyclicity--1`) -/
@[stacks 0A4B]
theorem Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity (hΛ : IsAddTorsion Λ)
    (f : X ⟶ Y) [IsProper f] :
    Etale.HasTorsionBaseChange Λ f ↔ Etale.HasInjectiveAcyclicity Λ f :=
  ⟨Etale.HasTorsionBaseChange.hasInjectiveAcyclicity Λ f,
    Etale.HasInjectiveAcyclicity.hasTorsionBaseChange Λ hΛ f⟩

end AlgebraicGeometry
