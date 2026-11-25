/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.SwapEvPairing
public import WeilConjectures.TraceFormula.OrdinaryKunnethDevissage

/-!

# The Künneth–Verdier map along an open immersion

Let `X, Y, U` be separated `k`-schemes of finite type, `j : U ⟶ Y` an open immersion and
`G = 𝟙_X × j : X ⨯ U ⟶ X ⨯ Y`, again an open immersion
(`ProEtale.CondensedRing.isOpenImmersion_prodMap_left`). This file compares the Künneth–Verdier
maps `κ^Y_{M,N}` on `X ⨯ Y` and `κ^U_{M,N'}` on `X ⨯ U`
(`ProEtale.CondensedRing.kunnethVerdierMap`), the step of the dévissage of the Künneth–Verdier
theorem (blueprint `lemma-external-duality-trace-morphism--1`) along an open subscheme of `Y`.

## The compatibility of the exceptional Künneth map with restriction

The restrictions of the source and target of the exceptional Künneth map
`α^Y_M : M ⊠ ω_Y ⟶ Rp_X^! M` (`ProEtale.CondensedRing.exceptionalKunnethMap`) to `X ⨯ U` are
identified with those of `α^U_M`:
```
LG^* (M ⊠ ω_Y) ≅ LG^* Lp_X^* M ⊗ LG^* Lp_Y^* ω_Y ≅ Lp_X^* M ⊗ Lp_U^* Lj^* ω_Y ≅ M ⊠ ω_U,
LG^* Rp_X^! M ≅ RG^! Rp_X^! M ≅ R(G ≫ p_X)^! M = Rp_X^! M
```
(`ProEtale.CondensedRing.exceptionalKunnethSourceRestrictionIso`,
`ProEtale.CondensedRing.exceptionalKunnethTargetRestrictionIso`), using
`Lj^* ω_Y ≅ Rj^! ω_Y ≅ ω_U` (`ProEtale.CondensedRing.dualizingComplexUpperStarIso`). The
statement that they carry `LG^* α^Y_M` to `α^U_M`,
`ProEtale.CondensedRing.ExceptionalKunnethMapRestriction`, follows from the coherence of the six
functors; it is a hypothesis of the results below.

## Main results

- `ProEtale.CondensedRing.map_kunnethVerdierMap_comp_kunnethVerdierTargetRestrictionIso_hom`:
  under `ExceptionalKunnethMapRestriction`, the restriction `LG^* κ^Y_{M,N}` is
  `κ^U_{M, Lj^* N}`, through the isomorphisms
  `LG^* (M ⊠ D_Y N) ≅ M ⊠ D_U (Lj^* N)` and
  `LG^* RHom(Lp_Y^* N, Rp_X^! M) ≅ RHom(Lp_U^* Lj^* N, Rp_X^! M)`
  (`ProEtale.CondensedRing.kunnethVerdierSourceRestrictionIso`,
  `ProEtale.CondensedRing.kunnethVerdierTargetRestrictionIso`).
- `ProEtale.CondensedRing.isIso_map_kunnethVerdierMap_iff`: hence `LG^* κ^Y_{M,N}` is an
  isomorphism if and only if `κ^U_{M, Lj^* N}` is.
- `ProEtale.CondensedRing.isIso_kunnethVerdierMap_lowerShriek`: **extension by zero**. For
  `N' ∈ Dᵇc(U)`, if `κ^U_{M, Lj^* Rj_! N'}` is an isomorphism, so is `κ^Y_{M, Rj_! N'}`. Both its
  source and its target lie in the essential image of `RG_*`: the source by Verdier duality
  `D_Y Rj_! N' ≅ Rj_* RHom(N', Rj^! ω_Y)` (`ProEtale.CondensedRing.isIso_verdierExchange`) and
  the ordinary Künneth formula `M ⊠ Rj_* B ≅ RG_* (M ⊠ B)`
  (`ProEtale.CondensedRing.isIso_openKunnethMap`), the target by compact-support base change
  `Lp_Y^* Rj_! N' ≅ RG_! Lp_U^* N'` and Verdier duality for `G`. As `RG_*` is fully faithful,
  a morphism between such objects is an isomorphism as soon as its restriction along `G` is
  (`CategoryTheory.Adjunction.isIso_of_isIso_map_of_isIso_counit`).

## Implementation notes

The diagram chases are carried out for abstract monoidal categories in
`WeilConjectures.CategoryTheory.Monoidal.Closed.SwapEvPairing`. The tensor products of bounded
constructible complexes are elaborated in two ways: through the monoidal structure of the full
subcategory directly (`ObjectProperty.instMonoidalCategoryStructFullSubcategory`), as in the
statements of `WeilConjectures.TraceFormula.KunnethVerdier`, or through the projection of the
monoidal category instance `monoidalCategory_boundedConstructible`, as in the abstract lemmas.
The two are definitionally equal but comparing large terms built from them is very slow, so the
projection is made the preferred instance locally, and the final comparison with the statements
of `WeilConjectures.TraceFormula.KunnethVerdier` is made termwise, with `convert`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

-- see the implementation notes
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y U : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] in
/-- The product `𝟙 × j : X ⨯ U ⟶ X ⨯ Y` of an open immersion `j` is an open immersion, being the
base change of `j` along the second projection. -/
instance isOpenImmersion_prodMap_left (j : U ⟶ Y) [IsOpenImmersion j.left] :
    IsOpenImmersion (prod.map (𝟙 X) j).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_prod_snd_with_id j X).map (Over.forget _))
    (inferInstanceAs (IsOpenImmersion j.left))

/-! ### The compatibility of the exceptional Künneth map with restriction -/

/-- The restriction `Lj^* ω_Y ≅ ω_U` of the dualizing complex to an open subscheme: the inverse
of `Rj^! ≅ Lj^*` followed by `Rj^! ω_Y ≅ ω_U`. -/
noncomputable def dualizingComplexUpperStarIso (j : U ⟶ Y) [IsOpenImmersion j.left] :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        (dualizingComplex' ℓ Y) ≅ dualizingComplex' ℓ U :=
  (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).symm.app _ ≪≫
    dualizingComplexComp ℓ j

/-- The restriction to `X ⨯ U` of the source of the exceptional Künneth map:
`L(𝟙 × j)^* (M ⊠ ω_Y) ≅ M ⊠ ω_U`, from the monoidal structure of `L(𝟙 × j)^*`, the composition
isomorphisms of the pullbacks and `Lj^* ω_Y ≅ ω_U`. -/
noncomputable def exceptionalKunnethSourceRestrictionIso (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).obj
        (externalProduct ℓ M (dualizingComplex' ℓ Y)) ≅
      externalProduct ℓ M (dualizingComplex' ℓ U) :=
  (Functor.Monoidal.μIso _ _ _).symm ≪≫
    tensorIso ((prodMapUpperStarFstIso ℓ j).app M)
      ((prodMapUpperStarSndIso ℓ j).app _ ≪≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).mapIso (dualizingComplexUpperStarIso ℓ j))

/-- The isomorphism `exceptionalKunnethSourceRestrictionIso`, componentwise. -/
private lemma exceptionalKunnethSourceRestrictionIso_hom (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (exceptionalKunnethSourceRestrictionIso ℓ j M).hom =
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map (𝟙 X) j)) _ _ ≫ ((prodMapUpperStarFstIso ℓ j).hom.app M ⊗ₘ
        ((prodMapUpperStarSndIso ℓ j).hom.app _ ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (prod.snd : X ⨯ U ⟶ U)).map (dualizingComplexUpperStarIso ℓ j).hom)) :=
  rfl

/-- The restriction to `X ⨯ U` of the target of the exceptional Künneth map:
`L(𝟙 × j)^* Rp_X^! M ≅ R(𝟙 × j)^! Rp_X^! M ≅ R((𝟙 × j) ≫ p_X)^! M = Rp_X^! M`. -/
noncomputable def exceptionalKunnethTargetRestrictionIso (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).obj
        ((boundedConstructibleUpperShriek ℓ
          (prod.fst : X ⨯ Y ⟶ X)).obj M) ≅
      (boundedConstructibleUpperShriek ℓ
        (prod.fst : X ⨯ U ⟶ X)).obj M :=
  (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ (prod.map (𝟙 X) j)).symm.app _ ≪≫
    ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ (prod.map (𝟙 X) j) prod.fst).app M).symm ≪≫
    eqToIso (by rw [prod.map_fst, Category.comp_id])

/-- **Compatibility of the exceptional Künneth map with restriction to `X ⨯ U`** (a consequence
of the coherence of the six functors, used here as a hypothesis): under the identifications
`exceptionalKunnethSourceRestrictionIso` and `exceptionalKunnethTargetRestrictionIso`, the
restriction `L(𝟙 × j)^* α^Y_M` of the exceptional Künneth map is `α^U_M`. -/
def ExceptionalKunnethMapRestriction (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : Prop :=
  (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).map
      (exceptionalKunnethMap ℓ (Y := Y) M) ≫ (exceptionalKunnethTargetRestrictionIso ℓ j M).hom =
    (exceptionalKunnethSourceRestrictionIso ℓ j M).hom ≫ exceptionalKunnethMap ℓ (Y := U) M

/-- The exceptional restriction compatibility after precomposing with the tensor comparison. -/
private lemma μ_map_exceptionalKunnethMap_comp_restriction (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hα : ExceptionalKunnethMapRestriction ℓ j M) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)) _ _ ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).map
        (exceptionalKunnethMap ℓ (Y := Y) M) ≫ (exceptionalKunnethTargetRestrictionIso ℓ j M).hom =
      ((prodMapUpperStarFstIso ℓ j).hom.app M ⊗ₘ
        ((prodMapUpperStarSndIso ℓ j).hom.app _ ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (prod.snd : X ⨯ U ⟶ U)).map (dualizingComplexUpperStarIso ℓ j).hom)) ≫
        exceptionalKunnethMap ℓ (Y := U) M := by
  rw [hα, exceptionalKunnethSourceRestrictionIso_hom]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]

/-! ### Monoidality of the pullbacks -/

/-- The identification `Lf^* = Lf'^*` for `f = f'` is compatible with the tensor structures. -/
@[reassoc]
lemma μ_boundedConstructibleUpperStar_eqToHom_app {A B : Over (Spec (.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] {f f' : A ⟶ B}
    (hf : f = f') (h : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f =
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f')
    (K M : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
        K M ≫ (eqToHom h).app (K ⊗ M) =
      ((eqToHom h).app K ⊗ₘ (eqToHom h).app M) ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f')
          K M := by
  subst hf
  simp

/-- `L(𝟙 × j)^* Lp_Y^* ≅ Lp_U^* Lj^*` is the composite of the composition isomorphisms of the
pullbacks and of the identification along `(𝟙 × j) ≫ p_Y = p_U ≫ j`. -/
lemma prodMapUpperStarSndIso_hom_eq (j : U ⟶ Y) (h : boundedConstructibleUpperStar
    (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j ≫ prod.snd) =
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd ≫ j)) :
    (prodMapUpperStarSndIso (X := X) ℓ j).hom =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map (𝟙 X) j) prod.snd).inv ≫ eqToHom h ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ prod.snd j).hom := by
  unfold prodMapUpperStarSndIso
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]

-- the tensor structures of the composite pullbacks are compared through `(f ≫ g).left`
/-- The composition isomorphism `L(𝟙 × j)^* Lp_Y^* ≅ Lp_U^* Lj^*` is compatible with the tensor
structures of the pullbacks. -/
lemma μ_prodMapUpperStarSndIso_hom_app (j : U ⟶ Y)
    (A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map (𝟙 X) j))
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ Y ⟶ Y)).obj A)
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ Y ⟶ Y)).obj B) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).map
        (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ Y ⟶ Y)) A B) ≫
      (prodMapUpperStarSndIso ℓ j).hom.app (A ⊗ B) =
    ((prodMapUpperStarSndIso ℓ j).hom.app A ⊗ₘ (prodMapUpperStarSndIso ℓ j).hom.app B) ≫
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U))
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj A)
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj B) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).map
        (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)
          A B) := by
  have h : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.map (𝟙 X) j ≫ prod.snd) =
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd ≫ j) := by
    rw [prod.map_snd]
  simp only [prodMapUpperStarSndIso_hom_eq ℓ j h, NatTrans.comp_app,
    Functor.Monoidal.μ_comp_inv_app_of_δ_assoc _ _ _ _
      (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ
        (prod.map (𝟙 X) j) prod.snd),
    μ_boundedConstructibleUpperStar_eqToHom_app_assoc ℓ (prod.map_snd (𝟙 X) j) h,
    Functor.Monoidal.μ_comp_hom_app_of_δ _ _ _ _
      (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ
        prod.snd j),
    tensorHom_comp_tensorHom_assoc]

/-- The pullback `Lf^*` on bounded constructible complexes is compatible with the Koszul
braidings, in terms of its tensor structure. -/
lemma μ_boundedConstructibleUpperStar_braiding {A B : Over (Spec (.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (f : A ⟶ B)
    (K M : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
        K M ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map (β_ K M).hom =
      (β_ ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K)
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)).hom ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
          M K := by
  rw [← cancel_mono (Functor.OplaxMonoidal.δ
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) M K),
    Category.assoc, Category.assoc, boundedConstructibleUpperStar_map_braiding_hom_δ,
    Functor.Monoidal.μ_δ, Category.comp_id, Functor.Monoidal.μ_δ_assoc]

/-! ### Restriction of the Künneth–Verdier map -/

/-- The restriction of the Verdier dual to an open subscheme, `Lj^* D_Y N ≅ D_U (Lj^* N)`: the
internal-hom comparison of `Lj^*` (an isomorphism for open `j`) followed by `Lj^* ω_Y ≅ ω_U`. -/
noncomputable def verdierDualUpperStarIso (j : U ⟶ Y) [IsOpenImmersion j.left]
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        (verdierDual ℓ N) ≅
      verdierDual ℓ
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj N) :=
  haveI := isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion
    ℓ j N
  asIso ((Functor.LaxMonoidal.ihomComparison
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j) N).app
        (dualizingComplex' ℓ Y)) ≪≫
    (ihom _).mapIso (dualizingComplexUpperStarIso ℓ j)

/-- The isomorphism `verdierDualUpperStarIso` is the internal-hom comparison followed by
`Lj^* ω_Y ≅ ω_U`. -/
lemma verdierDualUpperStarIso_hom (j : U ⟶ Y) [IsOpenImmersion j.left]
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (verdierDualUpperStarIso ℓ j N).hom =
      (Functor.LaxMonoidal.ihomComparison
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j) N).app
          (dualizingComplex' ℓ Y) ≫
        (ihom _).map (dualizingComplexUpperStarIso ℓ j).hom :=
  rfl

/-- The restriction to `X ⨯ U` of the source of the Künneth–Verdier map:
`L(𝟙 × j)^* (M ⊠ D_Y N) ≅ M ⊠ D_U (Lj^* N)`. -/
noncomputable def kunnethVerdierSourceRestrictionIso (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).obj
        (externalProduct ℓ M (verdierDual ℓ N)) ≅
      externalProduct ℓ M (verdierDual ℓ
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj N)) :=
  (Functor.Monoidal.μIso _ _ _).symm ≪≫
    tensorIso ((prodMapUpperStarFstIso ℓ j).app M)
      ((prodMapUpperStarSndIso ℓ j).app _ ≪≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).mapIso (verdierDualUpperStarIso ℓ j N))

/-- The isomorphism `kunnethVerdierSourceRestrictionIso`, componentwise. -/
lemma kunnethVerdierSourceRestrictionIso_hom (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (kunnethVerdierSourceRestrictionIso ℓ j M N).hom =
      Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map (𝟙 X) j)) _ _ ≫ ((prodMapUpperStarFstIso ℓ j).hom.app M ⊗ₘ
        ((prodMapUpperStarSndIso ℓ j).hom.app _ ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (prod.snd : X ⨯ U ⟶ U)).map (verdierDualUpperStarIso ℓ j N).hom)) :=
  rfl

/-- The restriction to `X ⨯ U` of the target of the Künneth–Verdier map:
`L(𝟙 × j)^* RHom(Lp_Y^* N, Rp_X^! M) ≅ RHom(Lp_U^* Lj^* N, Rp_X^! M)`, from the internal-hom
comparison of `L(𝟙 × j)^*` (an isomorphism, `𝟙 × j` being an open immersion),
`exceptionalKunnethTargetRestrictionIso` and `L(𝟙 × j)^* Lp_Y^* ≅ Lp_U^* Lj^*`. -/
noncomputable def kunnethVerdierTargetRestrictionIso (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).obj
        ((ihom ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ Y ⟶ Y)).obj N)).obj
          ((boundedConstructibleUpperShriek ℓ
            (prod.fst : X ⨯ Y ⟶ X)).obj M)) ≅
      (ihom ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj N))).obj
        ((boundedConstructibleUpperShriek ℓ
          (prod.fst : X ⨯ U ⟶ X)).obj M) :=
  haveI := isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion
    ℓ (prod.map (𝟙 X) j)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.snd : X ⨯ Y ⟶ Y)).obj N)
  asIso ((Functor.LaxMonoidal.ihomComparison
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j))
        _).app _) ≪≫
    (ihom _).mapIso (exceptionalKunnethTargetRestrictionIso ℓ j M) ≪≫
    preIsoApp ((prodMapUpperStarSndIso ℓ j).app N) _

/-- The isomorphism `kunnethVerdierTargetRestrictionIso`, componentwise. -/
lemma kunnethVerdierTargetRestrictionIso_hom (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (kunnethVerdierTargetRestrictionIso ℓ j M N).hom =
      (Functor.LaxMonoidal.ihomComparison
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j))
          _).app _ ≫
        (ihom _).map (exceptionalKunnethTargetRestrictionIso ℓ j M).hom ≫
        (pre ((prodMapUpperStarSndIso ℓ j).app N).inv).app _ :=
  rfl

/-- The Künneth–Verdier pairing is an instance of `swapEvPairing`. -/
lemma kunnethVerdierPairing_eq_swapEvPairing (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    kunnethVerdierPairing ℓ M N = swapEvPairing
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y))
      (exceptionalKunnethMap ℓ M) N :=
  rfl

/-- The Künneth–Verdier map is the transpose of an instance of `swapEvPairing`. -/
lemma kunnethVerdierMap_eq_curry_swapEvPairing (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    kunnethVerdierMap ℓ M N = curry (swapEvPairing
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y))
      (exceptionalKunnethMap ℓ M) N) :=
  rfl

-- the final comparison with the statement of `kunnethVerdierMap` is made termwise
/-- **Restriction of the Künneth–Verdier map to `X ⨯ U`**: if the exceptional Künneth map is
compatible with restriction (`ExceptionalKunnethMapRestriction`), then for every `N` the square
```
L(𝟙 × j)^* (M ⊠ D_Y N) ──L(𝟙 × j)^* κ^Y_{M,N}──▶ L(𝟙 × j)^* RHom(Lp_Y^* N, Rp_X^! M)
          │                                                  │
          ▼                                                  ▼
 M ⊠ D_U (Lj^* N) ─────────κ^U_{M, Lj^* N}────────▶ RHom(Lp_U^* Lj^* N, Rp_X^! M)
```
commutes. -/
theorem map_kunnethVerdierMap_comp_kunnethVerdierTargetRestrictionIso_hom
    (j : U ⟶ Y) [IsOpenImmersion j.left] (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hα : ExceptionalKunnethMapRestriction ℓ j M)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j)).map
        (kunnethVerdierMap ℓ (Y := Y) M N) ≫ (kunnethVerdierTargetRestrictionIso ℓ j M N).hom =
      (kunnethVerdierSourceRestrictionIso ℓ j M N).hom ≫ kunnethVerdierMap ℓ (Y := U) M
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj N) := by
  simp only [kunnethVerdierTargetRestrictionIso_hom, kunnethVerdierMap_eq_curry_swapEvPairing]
  refine map_curry_comp
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j))
    (swapEvPairing (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.snd : X ⨯ Y ⟶ Y)) (exceptionalKunnethMap ℓ (Y := Y) M) N)
    (swapEvPairing (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.snd : X ⨯ U ⟶ U)) (exceptionalKunnethMap ℓ (Y := U) M)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj N))
    ((prodMapUpperStarSndIso ℓ j).app N) (kunnethVerdierSourceRestrictionIso ℓ j M N).hom
    (exceptionalKunnethTargetRestrictionIso ℓ j M).hom ?_
  simp only [kunnethVerdierSourceRestrictionIso_hom, verdierDualUpperStarIso_hom]
  have key := μ_map_swapEvPairing
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y))
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ U ⟶ U))
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.map (𝟙 X) j))
    (μ_boundedConstructibleUpperStar_braiding ℓ (prod.map (𝟙 X) j))
    (prodMapUpperStarSndIso ℓ j).hom (μ_prodMapUpperStarSndIso_hom_app ℓ j)
    ((prodMapUpperStarFstIso ℓ j).hom.app M) (dualizingComplexUpperStarIso ℓ j).hom
    (exceptionalKunnethTargetRestrictionIso ℓ j M).hom (exceptionalKunnethMap ℓ (Y := Y) M)
    (exceptionalKunnethMap ℓ (Y := U) M)
    (μ_map_exceptionalKunnethMap_comp_restriction ℓ j M hα) N
  convert key <;> rfl

/-- **Restriction of the Künneth–Verdier map to `X ⨯ U`**: if the exceptional Künneth map is
compatible with restriction, the restriction `L(𝟙 × j)^* κ^Y_{M,N}` is an isomorphism if and only
if `κ^U_{M, Lj^* N}` is. -/
theorem isIso_map_kunnethVerdierMap_iff (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hα : ExceptionalKunnethMapRestriction ℓ j M)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.map (𝟙 X) j)).map (kunnethVerdierMap ℓ (Y := Y) M N)) ↔
      IsIso (kunnethVerdierMap ℓ (Y := U) M
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj N)) := by
  rw [← isIso_comp_right_iff _ (kunnethVerdierTargetRestrictionIso ℓ j M N).hom,
    map_kunnethVerdierMap_comp_kunnethVerdierTargetRestrictionIso_hom ℓ j M hα N,
    isIso_comp_left_iff]

/-! ### Extension by zero -/

/-- For an open immersion `i`, the counit `Li^* Ri_* ⟶ 𝟭` on bounded constructible complexes is an
isomorphism: `Li^*` has the fully faithful left adjoint `i_!`, so its right adjoint `Ri_*` is
fully faithful as well. -/
instance isIso_boundedConstructibleUpperStarLowerStarAdjunction_counit_of_isOpenImmersion
    {A B : Over (Spec (.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (i : A ⟶ B)
    [IsOpenImmersion i.left] :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      i).counit :=
  (Adjunction.Triple.mk
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ i)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      i)).isIso_unit_iff_isIso_counit.1 inferInstance

/-- The source `M ⊠ D_Y (Rj_! N')` of the Künneth–Verdier map lies in the essential image of
`R(𝟙 × j)_*`: by Verdier duality `D_Y Rj_! N' ≅ Rj_* RHom(N', Rj^! ω_Y)` and the ordinary Künneth
formula `M ⊠ Rj_* B ≅ R(𝟙 × j)_* (M ⊠ B)`. -/
noncomputable def kunnethVerdierSourceLowerShriekIso (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N' : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ M (verdierDual ℓ
        ((boundedConstructibleLowerShriek ℓ j).obj N')) ≅
      (boundedConstructibleLowerStar ℓ (prod.map (𝟙 X) j)).obj
        (externalProduct ℓ M ((ihom N').obj
          ((boundedConstructibleUpperShriek ℓ j).obj
            (dualizingComplex ℓ Y)))) :=
  haveI := isIso_verdierExchange ℓ j N' (dualizingComplex ℓ Y)
  haveI := isIso_openKunnethMap ℓ (X := X) j M ((ihom N').obj
    ((boundedConstructibleUpperShriek ℓ j).obj
      (dualizingComplex ℓ Y)))
  whiskerLeftIso _ ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.snd : X ⨯ Y ⟶ Y)).mapIso
        (asIso (verdierExchange ℓ j N' (dualizingComplex ℓ Y))).symm) ≪≫
    asIso (openKunnethMap ℓ j M _)

/-- The target `RHom(Lp_Y^* Rj_! N', Rp_X^! M)` of the Künneth–Verdier map lies in the essential
image of `R(𝟙 × j)_*`: by compact-support base change `Lp_Y^* Rj_! N' ≅ R(𝟙 × j)_! Lp_U^* N'` and
Verdier duality `RHom(R(𝟙 × j)_! K, L) ≅ R(𝟙 × j)_* RHom(K, R(𝟙 × j)^! L)`. -/
noncomputable def kunnethVerdierTargetLowerShriekIso (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N' : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (ihom ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (prod.snd : X ⨯ Y ⟶ Y)).obj
        ((boundedConstructibleLowerShriek ℓ j).obj N'))).obj
        ((boundedConstructibleUpperShriek ℓ
          (prod.fst : X ⨯ Y ⟶ X)).obj M) ≅
      (boundedConstructibleLowerStar ℓ (prod.map (𝟙 X) j)).obj
        ((ihom ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (prod.snd : X ⨯ U ⟶ U)).obj N')).obj
          ((boundedConstructibleUpperShriek ℓ
            (prod.map (𝟙 X) j)).obj
            ((boundedConstructibleUpperShriek ℓ
              (prod.fst : X ⨯ Y ⟶ X)).obj M))) :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (IsPullback.of_prod_snd_with_id j X)
  haveI := isIso_verdierExchange ℓ (prod.map (𝟙 X) j)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.snd : X ⨯ U ⟶ U)).obj N')
    ((boundedConstructibleUpperShriek ℓ
      (prod.fst : X ⨯ Y ⟶ X)).obj M)
  preIsoApp (asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
      (IsPullback.of_prod_snd_with_id j X)).app N')) _ ≪≫
    (asIso (verdierExchange ℓ (prod.map (𝟙 X) j) _ _)).symm

/-- **The Künneth–Verdier map for an extension by zero.** Let `j : U ⟶ Y` be an open immersion
such that the exceptional Künneth map is compatible with restriction to `X ⨯ U`. For
`N' ∈ Dᵇc(U)`, if `κ^U_{M, Lj^* Rj_! N'}` is an isomorphism, then so is `κ^Y_{M, Rj_! N'}`: its
restriction to `X ⨯ U` is an isomorphism (`isIso_map_kunnethVerdierMap_iff`), and its source and
target lie in the essential image of the fully faithful `R(𝟙 × j)_*`
(`kunnethVerdierSourceLowerShriekIso`, `kunnethVerdierTargetLowerShriekIso`). -/
theorem isIso_kunnethVerdierMap_lowerShriek (j : U ⟶ Y) [IsOpenImmersion j.left]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hα : ExceptionalKunnethMapRestriction ℓ j M)
    (N' : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : IsIso (kunnethVerdierMap ℓ (Y := U) M
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        ((boundedConstructibleLowerShriek ℓ j).obj N')))) :
    IsIso (kunnethVerdierMap ℓ (Y := Y) M
      ((boundedConstructibleLowerShriek ℓ j).obj N')) := by
  have := (isIso_map_kunnethVerdierMap_iff ℓ j M hα _).2 h
  exact Adjunction.isIso_of_isIso_map_of_isIso_counit
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (prod.map (𝟙 X) j))
    (kunnethVerdierSourceLowerShriekIso ℓ j M N') (kunnethVerdierTargetLowerShriekIso ℓ j M N') _

end AlgebraicGeometry.ProEtale.CondensedRing
