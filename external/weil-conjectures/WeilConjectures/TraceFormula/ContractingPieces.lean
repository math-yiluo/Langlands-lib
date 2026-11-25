/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GraphPieces
public import WeilConjectures.TraceFormula.OpenSquare

/-!

# The pieces of a correspondence at a point with reduced fibre

Let `c = (c₁, c₂) : C ⟶ X × X` be an endocorrespondence of `(X, K)` with coefficient map
`u : Lc₂^* K ⟶ Rc₁^! K`, and let `x` be a rational point of `X` with open complement
`j : U = X ∖ {x} ⟶ X`. If `{x}` is `c`-invariant, `c₁⁻¹(x) ⊆ c₂⁻¹(x)`, equivalently
`V = c₂⁻¹(U) ⊆ W = c₁⁻¹(U)`, then `u` induces a coefficient map on the open piece
`K^U = j_! Lj^* K` (blueprint `proposition-additivity-trace-classes--2`,
`proposition-additivity-trace-classes--2`):

* `u^U = [j]_! (u|_U) : Lc₂^* K^U ⟶ Rc₁^! K^U`
  (`ProEtale.CondensedRing.Correspondence.pointOpenPieceCoeff`): the open base change
  `Lc₂^* j_! ≅ j_{V!} Lc_{2,V}^*` followed by the `j_{V!} ⊣ Lj_V^*` adjoint of the restriction
  ```
  Lc_{2,V}^* Lj^* K ≅ Lj_V^* Lc₂^* K --u--> Lj_V^* Rc₁^! K ≅ Lι^* Rc_{1,W}^! Lj^* K
    ⟶ Lι^* Rc_{1,W}^! Lj^* j_! Lj^* K ≅ Lj_V^* Rc₁^! K^U
  ```
  of `u` to the open correspondence `(c_{1,W} ∘ ι, c_{2,V}) : V ⟶ U × U`, where `ι : V ⟶ W` is
  the inclusion and the restriction of `Rc₁^!` to `W` is
  `Lj_W^* Rc₁^! ≅ Rj_W^! Rc₁^! ≅ R(c₁ ∘ j_W)^! = R(j ∘ c_{1,W})^! ≅ Rc_{1,W}^! Rj^!
  ≅ Rc_{1,W}^! Lj^*`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekOpenRestrict`).

If moreover `c₁⁻¹(x)` is a single reduced point `y` with `c₂(y) = x`, the closed piece
`K^Z = Rx_* Lx^* K` carries the proper pushforward along `(x, y)` of the restricted coefficient
map `u_Z : K_x ⟶ K_x` (`Correspondence.restrictedClosedPieceDiagram`, in
`WeilConjectures.TraceFormula.LocalTermLocality`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### Restriction of the exceptional inverse image to an open subscheme -/

section OpenRestrict

variable (ℓ) {W Y U : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsSeparated W.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]

/-- The restriction of the exceptional inverse image to open subschemes: for a commutative square
`g_W ≫ j = j_W ≫ g` with `j`, `j_W` open immersions,
`Lj_W^* Rg^! ≅ Rj_W^! Rg^! ≅ R(j_W ≫ g)^! = R(g_W ≫ j)^! ≅ Rg_W^! Rj^! ≅ Rg_W^! Lj^*`. -/
noncomputable def boundedConstructibleUpperShriekOpenRestrict {jW : W ⟶ Y} {g : Y ⟶ X}
    {gW : W ⟶ U} {j : U ⟶ X} [IsOpenImmersion jW.left] [IsOpenImmersion j.left]
    (w : gW ≫ j = jW ≫ g) :
    boundedConstructibleUpperShriek ℓ g ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ jW ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        boundedConstructibleUpperShriek ℓ gW :=
  Functor.isoWhiskerLeft _ (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ jW).symm ≪≫
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ jW g).symm ≪≫
    eqToIso (by rw [w]) ≪≫
    boundedConstructibleUpperShriekComp_padicAlgCl ℓ gW j ≪≫
    Functor.isoWhiskerRight (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j) _

end OpenRestrict

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)
  (x : RationalPoint X)

/-! ### The open piece -/

/-- The restriction
```
Lc_{2,V}^* Lj^* K ≅ Lj_V^* Lc₂^* K --u--> Lj_V^* Rc₁^! K ≅ Lι^* Lj_W^* Rc₁^! K
  ≅ Lι^* Rc_{1,W}^! Lj^* K ⟶ Lι^* Rc_{1,W}^! Lj^* K^U ≅ Lι^* Lj_W^* Rc₁^! K^U ≅ Lj_V^* Rc₁^! K^U
```
of `u` to the preimage `V = c₂⁻¹(X ∖ {x})`, contained in `W = c₁⁻¹(X ∖ {x})`, followed by the
unit `Lj^* K ⟶ Lj^* j_! Lj^* K` of `j_! ⊣ Lj^*`. -/
noncomputable def pointOpenRestriction
    (hle : c.c₂.left ⁻¹ᵁ pointComplOpens x ≤ c.c₁.left ⁻¹ᵁ pointComplOpens x) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (preimagePointComplRestrict c.c₂ x)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (pointComplι x)).obj
          K) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (preimagePointComplι c.c₂ x)).obj
        ((boundedConstructibleUpperShriek ℓ c.c₁).obj
          (pointOpenPiece K x)) :=
  (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (preimagePointComplRestrict c.c₂ x) (pointComplι x)).inv.app K ≫
    eqToHom (by rw [(isPullback_preimagePointComplRestrict c.c₂ x).w]) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (preimagePointComplι c.c₂ x) c.c₂).hom.app K ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (preimagePointComplι c.c₂ x)).map c.u ≫
    eqToHom (by rw [preimagePointComplHomOfLE_ι hle]) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (preimagePointComplHomOfLE hle) (preimagePointComplι c.c₁ x)).hom.app _ ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (preimagePointComplHomOfLE hle)).map
      ((boundedConstructibleUpperShriekOpenRestrict ℓ
          (isPullback_preimagePointComplRestrict c.c₁ x).w).hom.app K ≫
        (boundedConstructibleUpperShriek ℓ
          (preimagePointComplRestrict c.c₁ x)).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ (pointComplι x)).unit.app _) ≫
        (boundedConstructibleUpperShriekOpenRestrict ℓ
          (isPullback_preimagePointComplRestrict c.c₁ x).w).inv.app (pointOpenPiece K x)) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (preimagePointComplHomOfLE hle) (preimagePointComplι c.c₁ x)).inv.app _ ≫
    eqToHom (by rw [preimagePointComplHomOfLE_ι hle])

/-- The *open piece coefficient* `u^U = [j]_! (u|_U) : Lc₂^* K^U ⟶ Rc₁^! K^U` of a
correspondence for which the complement `X ∖ {x}` of a rational point satisfies
`c₂⁻¹(X ∖ {x}) ⊆ c₁⁻¹(X ∖ {x})`: the open base change `Lc₂^* j_! ≅ j_{V!} Lc_{2,V}^*` followed by
the `j_{V!} ⊣ Lj_V^*` adjoint of the restriction `pointOpenRestriction` of `u`. -/
noncomputable def pointOpenPieceCoeff
    (hle : c.c₂.left ⁻¹ᵁ pointComplOpens x ≤ c.c₁.left ⁻¹ᵁ pointComplOpens x) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj
        (pointOpenPiece K x) ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj
        (pointOpenPiece K x) :=
  (openSquareExchange ℓ (isPullback_preimagePointComplRestrict c.c₂ x)).hom.app _ ≫
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ (preimagePointComplι c.c₂ x)).homEquiv _ _).symm
      (c.pointOpenRestriction x hle)

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
