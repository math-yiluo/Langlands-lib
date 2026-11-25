/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PointComplement
public import WeilConjectures.TraceFormula.TraceClassAdditivity

/-!

# The pieces of a graph correspondence at a fixed rational point

Let `h : X ⟶ X` be an endomorphism, `v : Lh^* K ⟶ K` a map and `x` a rational point fixed by
`h`, with open complement `j : U = X ∖ {x} ⟶ X`. The closed subscheme `{x}` is invariant under
the graph correspondence `(𝟙, h)`, and `v` induces coefficient maps on the pieces
```
K^Z = Rx_* Lx^* K,        K^U = j_! Lj^* K
```
of the open–closed triangle `K^U ⟶ K ⟶ K^Z ⟶` (blueprint `proposition-additivity-trace-classes--2`,
`proposition-additivity-trace-classes--2`):

* `u^Z = [x, x]_! v_x`, the proper pushforward along the diagram `(x, x)` of the point
  correspondence `(s, 𝟙, 𝟙)` with coefficient the stalk map `v_x : K_x ⟶ K_x`
  (`ProEtale.CondensedRing.Correspondence.graphClosedPieceCoeff`);
* `u^U = [j]_! (v|_U)`, the extension by zero of the restriction of `v` to the open
  correspondence on `V = h⁻¹(U) ⊆ U`:
  ```
  Lh^* j_! Lj^* K ≅ j_{V!} Lh_V^* Lj^* K ≅ j_! ι_! Lh_V^* Lj^* K ⟶ j_! Lj^* K,
  ```
  open base change for the cartesian square `h_V ≫ j = j_V ≫ h`, the composition isomorphism of
  the extensions by zero for `j_V = ι ≫ j`, and the `ι_! ⊣ Lι^*` adjoint of
  `Lh_V^* Lj^* K ≅ Lj_V^* Lh^* K --v--> Lj_V^* K ≅ Lι^* Lj^* K`
  (`ProEtale.CondensedRing.Correspondence.graphOpenPieceCoeff`). The square need not be
  cartesian for `ι`: `h` may map other points to `x`.

The trace class of `v` is the sum of the trace classes of `u^Z` and `u^U`
(`ProEtale.CondensedRing.Correspondence.traceClass_ofGraph_eq_add` in
`WeilConjectures.TraceFormula.PieceAdditivity`, blueprint `proposition-additivity-trace-classes--2`,
item 1).

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

/-! ### The preimage of the complement of a fixed point -/

section Preimage

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- A point fixed by `h` has no preimage in its complement: `h⁻¹(X ∖ {x}) ⊆ X ∖ {x}`. -/
lemma preimage_pointComplOpens_le {h : X ⟶ X} {x : RationalPoint X} (hx : x ≫ h = x) :
    h.left ⁻¹ᵁ pointComplOpens x ≤ pointComplOpens x := by
  intro y hy
  simp only [pointComplOpens, Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_mk,
    Set.mem_compl_iff, Set.mem_range, not_exists] at hy ⊢
  intro z hz
  refine hy z ?_
  rw [← hz, ← Scheme.Hom.comp_apply, ← Over.comp_left, hx]

/-- The inclusion `ι : h⁻¹(X ∖ {x}) ⟶ X ∖ {x}` for a point `x` fixed by `h`. -/
noncomputable def pointComplPreimageι {h : X ⟶ X} {x : RationalPoint X} (hx : x ≫ h = x) :
    preimagePointCompl h x ⟶ pointCompl x :=
  Over.homMk (X.left.homOfLE (preimage_pointComplOpens_le hx)) (by
    change _ ≫ (pointComplOpens x).ι ≫ X.hom = _
    rw [Scheme.homOfLE_ι_assoc]
    rfl)

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
lemma pointComplPreimageι_comp_left {h : X ⟶ X} {x : RationalPoint X} (hx : x ≫ h = x) :
    (pointComplPreimageι hx ≫ pointComplι x).left = (h.left ⁻¹ᵁ pointComplOpens x).ι :=
  Scheme.homOfLE_ι _ (preimage_pointComplOpens_le hx)

instance {h : X ⟶ X} {x : RationalPoint X} (hx : x ≫ h = x) :
    IsOpenImmersion (pointComplPreimageι hx).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE (preimage_pointComplOpens_le hx)))

instance {h : X ⟶ X} {x : RationalPoint X} (hx : x ≫ h = x) :
    IsOpenImmersion (pointComplPreimageι hx ≫ pointComplι x).left := by
  rw [pointComplPreimageι_comp_left]
  infer_instance

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- The square `h_V ≫ j = j_V ≫ h` of the restriction of `h` to `V = h⁻¹(X ∖ {x})` is
cartesian. -/
lemma isPullback_preimagePointComplRestrict_of_comp_eq {h : X ⟶ X} {x : RationalPoint X}
    (hx : x ≫ h = x) :
    IsPullback (preimagePointComplRestrict h x) (pointComplPreimageι hx ≫ pointComplι x)
      (pointComplι x) h := by
  have w : preimagePointComplRestrict h x ≫ pointComplι x =
      (pointComplPreimageι hx ≫ pointComplι x) ≫ h := by
    ext1
    rw [Over.comp_left, Over.comp_left, pointComplPreimageι_comp_left]
    exact morphismRestrict_ι _ _
  refine IsPullback.of_map (Over.forget _) w ?_
  have := isPullback_morphismRestrict h.left (pointComplOpens x)
  change IsPullback (h.left ∣_ pointComplOpens x) (pointComplPreimageι hx ≫ pointComplι x).left
    (pointComplOpens x).ι h.left
  rw [pointComplPreimageι_comp_left hx]
  exact this

end Preimage

namespace Correspondence

variable (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-! ### The stalk map -/

/-- The *stalk map* `v_x : K_x ≅ (Lh^* K)_x ⟶ K_x` of a map `v : Lh^* K ⟶ K` at a rational
point `x` fixed by `h`, through `Lx^* Lh^* ≅ L(x ≫ h)^* = Lx^*`. -/
noncomputable def graphStalkMap (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (x : RationalPoint X) (hx : x ≫ h = x) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K :=
  eqToHom (by rw [hx]) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x h).hom.app K ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).map v

/-- The stalk map of a coefficient map transported along an equality of objects. -/
lemma graphStalkMap_eqToHom {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (e : A = B)
    (h : X ⟶ X)
    (w : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj B ⟶ B)
    (x : RationalPoint X) (hx : x ≫ h = x) :
    graphStalkMap A h
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map (eqToHom e) ≫
          w ≫ eqToHom e.symm) x hx =
      eqToHom (by rw [e]) ≫ graphStalkMap B h w x hx ≫ eqToHom (by rw [e]) := by
  subst e
  simp

variable {h : X ⟶ X}
  (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
  {x : RationalPoint X} (hx : x ≫ h = x)

/-! ### The closed piece -/

/-- The *closed piece* `K^Z = Rx_* Lx^* K` of `K` at a rational point `x`. -/
noncomputable abbrev pointClosedPiece (x : RationalPoint X) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleLowerStar ℓ x).obj
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)

/-- The proper pushforward diagram `(x, x)` from the point correspondence `(s, 𝟙, 𝟙)` of the
stalk map `v_x` to the graph `(𝟙, h)`: a diagram since `x ≫ 𝟙 = 𝟙 ≫ x` and `x ≫ h = 𝟙 ≫ x`. -/
noncomputable abbrev graphClosedPieceDiagram :
    (ofEnd _ (graphStalkMap K h v x hx)).ProperPushforwardDiagram X where
  f := x
  D := X
  b₁ := 𝟙 X
  b₂ := h
  g := x
  w₁ := by
    rw [Category.comp_id]
    exact (Category.id_comp x).symm
  w₂ := by
    rw [hx]
    exact (Category.id_comp x).symm

/-- The *closed piece coefficient* `u^Z = [x, x]_! v_x : Lh^* K^Z ⟶ R(𝟙)^! K^Z`: the coefficient
pushforward of the stalk map along the proper pushforward diagram `(x, x)`. -/
noncomputable def graphClosedPieceCoeff :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj
        (pointClosedPiece K x) ⟶
      (boundedConstructibleUpperShriek ℓ (𝟙 X)).obj
        (pointClosedPiece K x) :=
  (graphClosedPieceDiagram K v hx).pushforwardCoeff

/-! ### The open piece -/

/-- The *open piece* `K^U = j_! Lj^* K` of `K` along the open complement `j : X ∖ {x} ⟶ X` of a
rational point. -/
noncomputable abbrev pointOpenPiece (x : RationalPoint X) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointComplι x)).obj
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (pointComplι x)).obj K)

/-- The restriction `Lh_V^* Lj^* K ≅ Lj_V^* Lh^* K --v--> Lj_V^* K ≅ Lι^* Lj^* K` of `v` to the
open correspondence on `V = h⁻¹(X ∖ {x})`. -/
noncomputable def graphOpenRestriction :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (preimagePointComplRestrict h x)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (pointComplι x)).obj
          K) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (pointComplPreimageι hx)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (pointComplι x)).obj
          K) :=
  (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (preimagePointComplRestrict h x) (pointComplι x)).inv.app K ≫
    eqToHom (by rw [(isPullback_preimagePointComplRestrict_of_comp_eq hx).w]) ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointComplPreimageι hx ≫ pointComplι x) h).hom.app K ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointComplPreimageι hx ≫ pointComplι x)).map v ≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointComplPreimageι hx) (pointComplι x)).hom.app K

/-- The *open piece coefficient* `u^U = [j]_! (v|_U) : Lh^* K^U ⟶ K^U`:
```
Lh^* j_! Lj^* K ≅ j_{V!} Lh_V^* Lj^* K ≅ j_! ι_! Lh_V^* Lj^* K ⟶ j_! Lj^* K,
```
open base change in the cartesian square `h_V ≫ j = j_V ≫ h`, the composition isomorphism of the
extensions by zero for `j_V = ι ≫ j`, and `j_!` of the `ι_! ⊣ Lι^*` adjoint of the restriction
`graphOpenRestriction` of `v`. -/
noncomputable def graphOpenPieceCoeff :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj
        (pointOpenPiece K x) ⟶ pointOpenPiece K x :=
  (openSquareExchange ℓ (isPullback_preimagePointComplRestrict_of_comp_eq hx)).hom.app _ ≫
    (boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointComplPreimageι hx) (pointComplι x)).hom.app _ ≫
    (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (pointComplι x)).map
      (((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ (pointComplPreimageι hx)).homEquiv _ _).symm
        (graphOpenRestriction K v hx))

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
