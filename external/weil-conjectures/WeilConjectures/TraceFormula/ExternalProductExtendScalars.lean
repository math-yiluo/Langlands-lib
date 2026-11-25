/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparisonIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IhomCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper
public import WeilConjectures.TraceFormula.ExternalProductCoefficients

/-!

# Extension of scalars of the external product with the Verdier dual

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and write
`T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` for the extension of scalars on bounded
constructible complexes, the composite of `E ⊗ᴸ_{𝒪_E} -` and `ℚ̄_ℓ ⊗ᴸ_E -`
(`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgCl`). Let `K₀` be a bounded
constructible `𝒪_E`-complex on `X` with an isomorphism `e : T_X K₀ ≅ K` (an *integral model* of
`K`, blueprint `lemma-integral-models-rational-frobenius-correspondences`). This file identifies the
external product of `K` with its Verdier dual with the extension of scalars of the integral one:
```
T_{X ⨯ X} (K₀ ⊠ 𝔻 K₀) ≅ K ⊠ 𝔻 K
```
(`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgClExternalProductVerdierDualIso`).
This is the identification of the coefficients `P = K ⊠ 𝔻 K` of the supported restriction with
the extension of scalars of an integral `P₀` in the passage from integral to `ℚ̄_ℓ`-coefficients
of blueprint `lemma-vanishing-local-term-zero-stalk`.

It is assembled from the coefficient comparisons of blueprint
`proposition-six-operations-change-coefficients`:

* the pullback clause (`proposition-six-operations-change-coefficients` (1)),
  `ProEtale.CondensedRing.boundedConstructibleUpperStarIntegersToPadicAlgClIso`, the composite of
  the comparisons for `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ`;
* the tensor clause (`proposition-six-operations-change-coefficients` (1)): `T_X` is monoidal;
* the internal Hom clause (`proposition-six-operations-change-coefficients` (2)): the comparison
  `T_X RHom(A, B) ⟶ RHom(T_X A, T_X B)`, the mate of the tensorator
  (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), is an isomorphism
  (`ProEtale.CondensedRing.isIso_ihomComparison_boundedConstructibleIntegersToPadicAlgCl`);
* the dualizing complexes (`lemma-change-coefficients-exceptional-inverse-image`, applied to the
unit):
  `T_X ω_{X,𝒪_E} ≅ ω_X`
  (`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgClDualizingIso`).

The identification of the Verdier duals is compatible with the evaluation (trace) maps
`K ⊗ 𝔻 K ⟶ ω`
(`ProEtale.CondensedRing.μ_comp_map_ev_comp_boundedConstructibleIntegersToPadicAlgClDualizingIso`).

For `𝒪_E ⟶ E` these clauses are proved, `E ⊗ᴸ_{𝒪_E} -` being the rationalization of
`Dᵇc(X)⟦𝒪_E⟧`. For `E ⟶ ℚ̄_ℓ` the internal Hom and `f^!` clauses are the compatibilities
`ProEtale.CondensedRing.isIso_ihomComparison_constructibleToPadicAlgCl` and
`ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekToPadicAlgCl` required from
`chap-Construction-of-f`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The extension of scalars `T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -` on bounded constructible complexes: the
extension of scalars along `𝒪_E ⟶ E` followed by the one along `E ⟶ ℚ̄_ℓ`. -/
noncomputable abbrev boundedConstructibleIntegersToPadicAlgCl (X : Over (Spec (.of k))) :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-! ### Pullback -/

/-- **(Pull)** for `𝒪_E ⟶ ℚ̄_ℓ` (blueprint `proposition-six-operations-change-coefficients` (1)):
`Lf^*_{𝒪_E} ⋙ T_X ≅ T_Y ⋙ Lf^*_{ℚ̄_ℓ}`, the comparison for `𝒪_E ⟶ E` followed by the one for
`E ⟶ ℚ̄_ℓ`. -/
noncomputable def boundedConstructibleUpperStarIntegersToPadicAlgClIso (f : X ⟶ Y) :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ f ⋙
        boundedConstructibleIntegersToPadicAlgCl ℓ E X ≅
      boundedConstructibleIntegersToPadicAlgCl ℓ E Y ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleUpperStarExtendScalarsIso ℓ E f)
      (constructibleToPadicAlgCl X.left ℓ E) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleExtendScalars Y.left ℓ E)
      (boundedConstructibleUpperStarToPadicAlgClIso ℓ E f) ≪≫
    (Functor.associator _ _ _).symm

/-! ### External products -/

/-- The extension of scalars of an external product is the external product of the extensions of
scalars: `T(M₀ ⊠ N₀) ≅ T M₀ ⊠ T N₀ ≅ M ⊠ N` for isomorphisms `T M₀ ≅ M` and `T N₀ ≅ N`, by the
monoidal structure of `T` and the pullback comparisons for the two projections. -/
noncomputable def boundedConstructibleIntegersToPadicAlgClExternalProductIso
    {M₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
    {N₀ : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
    {M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (eM : (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj M₀ ≅ M)
    (eN : (boundedConstructibleIntegersToPadicAlgCl ℓ E Y).obj N₀ ≅ N) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (X ⨯ Y)).obj
        (PadicIntegersRingObj.boundedConstructibleExternalProduct ℓ E.1 M₀ N₀) ≅
      externalProduct ℓ M N :=
  (Functor.Monoidal.μIso (boundedConstructibleIntegersToPadicAlgCl ℓ E (X ⨯ Y)) _ _).symm ≪≫
    tensorIso
      ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E (prod.fst : X ⨯ Y ⟶ X)).app M₀ ≪≫
        (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).mapIso eM)
      ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E (prod.snd : X ⨯ Y ⟶ Y)).app N₀ ≪≫
        (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).mapIso eN)

/-! ### Dualizing complexes and Verdier duals -/

section Dualizing

variable {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (a : X ⟶ S)

/-- The extension of scalars of the integral dualizing complex is the dualizing complex:
`T ω_{X,𝒪_E} = T (Ra^! 𝒪_E) ≅ Ra^! (T 𝒪_E) ≅ Ra^! ℚ̄_ℓ = ω_X`, by the `f^!` clause of blueprint
`proposition-six-operations-change-coefficients`
(`lemma-change-coefficients-exceptional-inverse-image`) for `𝒪_E ⟶ E` and for `E ⟶ ℚ̄_ℓ`, and the
unit isomorphisms of the monoidal functors `E ⊗ᴸ_{𝒪_E} -` and `ℚ̄_ℓ ⊗ᴸ_E -`. -/
noncomputable def boundedConstructibleIntegersToPadicAlgClDualizingIso :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj
        (PadicIntegersRingObj.boundedConstructibleDualizingComplex ℓ E.1 a) ≅
      (boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _) :=
  have := isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E a
  (constructibleToPadicAlgCl X.left ℓ E).mapIso
      ((boundedConstructibleUpperShriekExtendScalarsIso ℓ E a).app (𝟙_ _) ≪≫
        (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E a).mapIso
          (Functor.Monoidal.εIso (boundedConstructibleExtendScalars S.left ℓ E)).symm) ≪≫
    (asIso (boundedConstructibleUpperShriekToPadicAlgCl ℓ E a)).app (𝟙_ _) ≪≫
    (boundedConstructibleUpperShriek ℓ a).mapIso
      (Functor.Monoidal.εIso (constructibleToPadicAlgCl S.left ℓ E)).symm

variable {K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (e : (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K₀ ≅ K)

/-- The extension of scalars of the integral Verdier dual is the Verdier dual:
`T 𝔻 K₀ = T RHom(K₀, ω_{X,𝒪_E}) ≅ RHom(T K₀, T ω_{X,𝒪_E}) ≅ RHom(K, ω_X) = 𝔻 K`, by the internal
Hom clause of blueprint `proposition-six-operations-change-coefficients` and the comparison of the
dualizing complexes. -/
noncomputable def boundedConstructibleIntegersToPadicAlgClVerdierDualIso :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj
        (PadicIntegersRingObj.boundedConstructibleVerdierDual ℓ E.1 a K₀) ≅
      (ihom K).obj ((boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)) :=
  have := isIso_ihomComparison_boundedConstructibleIntegersToPadicAlgCl ℓ E K₀
  Functor.LaxMonoidal.mapIhomObjIso _ e (boundedConstructibleIntegersToPadicAlgClDualizingIso ℓ E a)

/-- **The identification of the Verdier duals is compatible with the evaluation maps**: the
extension of scalars of the integral evaluation `K₀ ⊗ 𝔻 K₀ ⟶ ω_{X,𝒪_E}` is, under the tensorator
of `T`, the isomorphisms `T K₀ ≅ K`, `T 𝔻 K₀ ≅ 𝔻 K` and `T ω_{X,𝒪_E} ≅ ω_X`, the evaluation
`K ⊗ 𝔻 K ⟶ ω_X`. -/
lemma μ_comp_map_ev_comp_boundedConstructibleIntegersToPadicAlgClDualizingIso :
    Functor.LaxMonoidal.μ (boundedConstructibleIntegersToPadicAlgCl ℓ E X) K₀
        (PadicIntegersRingObj.boundedConstructibleVerdierDual ℓ E.1 a K₀) ≫
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
        ((ihom.ev K₀).app (PadicIntegersRingObj.boundedConstructibleDualizingComplex ℓ E.1 a)) ≫
      (boundedConstructibleIntegersToPadicAlgClDualizingIso ℓ E a).hom =
    (e.hom ⊗ₘ (boundedConstructibleIntegersToPadicAlgClVerdierDualIso ℓ E a e).hom) ≫
      (ihom.ev K).app ((boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)) := by
  have := isIso_ihomComparison_boundedConstructibleIntegersToPadicAlgCl ℓ E K₀
  exact Functor.LaxMonoidal.μ_comp_map_ev_comp_hom _ e _

end Dualizing

/-! ### The external product with the Verdier dual -/

variable {K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- **Extension of scalars of the external product with the Verdier dual**: for an integral model
`e : T K₀ ≅ K` of `K`, `T (K₀ ⊠ 𝔻 K₀) ≅ K ⊠ 𝔻 K`, the coefficients of the supported restriction
of blueprint `lemma-vanishing-local-term-zero-stalk` being the extension of scalars of integral
coefficients. -/
noncomputable def boundedConstructibleIntegersToPadicAlgClExternalProductVerdierDualIso
    (e : (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K₀ ≅ K) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (X ⨯ X)).obj
        (PadicIntegersRingObj.boundedConstructibleExternalProduct ℓ E.1 K₀
          (PadicIntegersRingObj.boundedConstructibleVerdierDual ℓ E.1 (toPoint X) K₀)) ≅
      externalProduct ℓ K (verdierDual ℓ K) :=
  boundedConstructibleIntegersToPadicAlgClExternalProductIso ℓ E e
    (boundedConstructibleIntegersToPadicAlgClVerdierDualIso ℓ E (toPoint X) e)

end AlgebraicGeometry.ProEtale.CondensedRing
