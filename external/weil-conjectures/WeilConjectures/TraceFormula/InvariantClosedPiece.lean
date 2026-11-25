/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingClosedPiece

/-!

# The closed piece of a correspondence along an invariant closed subscheme

Let `c = (c₁, c₂) : C ⟶ X × X` be an endocorrespondence of `(X, K)` with coefficient map
`u : Lc₂^* K ⟶ Rc₁^! K`, and let `i : Z ⟶ X` be a closed immersion. Let `i' : C_Z ⟶ C` be the
preimage `c₁⁻¹(Z)`, so that the square `i' ≫ c₁ = c_{1Z} ≫ i` is cartesian, and suppose that
`c₂` maps `C_Z` into `Z`, `i' ≫ c₂ = c_{2Z} ≫ i` (this forces `c₁⁻¹(Z) ⊆ c₂⁻¹(Z)`, and holds for
instance when `c₁⁻¹(Z)` is reduced and `c₁⁻¹(Z) ⊆ c₂⁻¹(Z)`). Then (blueprint
`lemma-lift-correspondence-invariant-decomposition`, `lemma-closed-piece-pushforward`):

* `u` restricts to a correspondence `c_Z = (C_Z, c_{1Z}, c_{2Z}, u_{|Z})` on `(Z, Li^* K)`
  (`ProEtale.CondensedRing.Correspondence.restrictClosed`), whose coefficient map
  `u_{|Z} : Lc_{2Z}^* Li^* K ⟶ Rc_{1Z}^! Li^* K`
  (`ProEtale.CondensedRing.restrictedCoeffOfIsPullback`) has exceptional adjoint
  `Rc_{1Z!} Lc_{2Z}^* Li^* K ≅ Li^* Rc₁_! Lc₂^* K --Li^* û--> Li^* K`
  (`ProEtale.CondensedRing.homEquiv_symm_restrictedCoeffOfIsPullback`);
* the pushforward `u_Z = [i, i']_! u_{|Z}` of `u_{|Z}` along the proper maps `i` and `i'`
  (`ProEtale.CondensedRing.Correspondence.closedPieceDiagram`), a coefficient map on the closed
  piece `K_Z = Ri_* Li^* K`, is compatible with `u` along the unit `η : K ⟶ Ri_* Li^* K`:
  `u_Z ∘ Lc₂^* η = Rc₁^! η ∘ u`
  (`ProEtale.CondensedRing.Correspondence.upperStar_map_unit_comp_closedPieceCoeff`).

This generalizes `Correspondence.restrictedClosedPieceDiagram` and
`Correspondence.upperStar_map_unit_comp_restrictedClosedPieceCoeff` from a rational point with
reduced fibre to an arbitrary closed subscheme.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-- The base change `i' : C_Z ⟶ C` of a proper morphism `i : Z ⟶ X` along `c₁ : C ⟶ X` over
a scheme `S` is proper. -/
lemma AlgebraicGeometry.isProper_left_of_isPullback {S : Scheme} {X C Z CZ : Over S}
    {c₁ : C ⟶ X} {i : Z ⟶ X} {i' : CZ ⟶ C} {c₁Z : CZ ⟶ Z} (sq : IsPullback i' c₁Z c₁ i)
    [IsProper i.left] : IsProper i'.left :=
  MorphismProperty.of_isPullback (P := @IsProper) (sq.flip.map (Over.forget _)) ‹_›

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Restriction

variable {X C Z CZ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType CZ.hom] [QuasiCompact CZ.hom] [IsSeparated CZ.hom]
  {c₁ c₂ : C ⟶ X} {i : Z ⟶ X} {i' : CZ ⟶ C} {c₁Z c₂Z : CZ ⟶ Z}

variable (sq : IsPullback i' c₁Z c₁ i) (w₂ : i' ≫ c₂ = c₂Z ≫ i)
  (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (u : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K ⟶
    (boundedConstructibleUpperShriek ℓ c₁).obj K)

/-- The identification `Lc_{2Z}^* Li^* K ≅ Li'^* Lc₂^* K` for `i' ≫ c₂ = c_{2Z} ≫ i`. -/
noncomputable def upperStarIsoOfComm :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂Z).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i').obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K) :=
  ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c₂Z i).app K).symm ≪≫
    eqToIso (by rw [w₂]) ≪≫
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i' c₂).app K

include sq in
/-- The *restriction* `u_{|Z} : Lc_{2Z}^* Li^* K ⟶ Rc_{1Z}^! Li^* K` of a coefficient map
`u : Lc₂^* K ⟶ Rc₁^! K` to a closed subscheme `i : Z ⟶ X`, along the cartesian square
`i' ≫ c₁ = c_{1Z} ≫ i` and `i' ≫ c₂ = c_{2Z} ≫ i` (blueprint `lemma-closed-piece-pushforward`):
```
Lc_{2Z}^* Li^* K ≅ Li'^* Lc₂^* K --Li'^* u--> Li'^* Rc₁^! K --β--> Rc_{1Z}^! Li^* K,
```
where `β` is the `Rc_{1Z!} ⊣ Rc_{1Z}^!` adjoint of
`Rc_{1Z!} Li'^* Rc₁^! K ≅ Li^* Rc₁_! Rc₁^! K --Li^* ε--> Li^* K` (compact-support base change in
the cartesian square). -/
noncomputable def restrictedCoeffOfIsPullback :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂Z).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) ⟶
      (boundedConstructibleUpperShriek ℓ c₁Z).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K) :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  (upperStarIsoOfComm w₂ K).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i').map u ≫
    (boundedConstructibleUpperShriekAdjunction ℓ c₁Z).homEquiv _ _
      ((asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)).inv.app
          ((boundedConstructibleUpperShriek ℓ c₁).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map
          ((boundedConstructibleUpperShriekAdjunction ℓ c₁).counit.app K))

/-- **The exceptional adjoint of the restricted coefficient map** (blueprint
`lemma-lift-correspondence-invariant-decomposition`, the closed piece): the
`Rc_{1Z!} ⊣ Rc_{1Z}^!` adjoint of `u_{|Z}` is
```
Rc_{1Z!} Lc_{2Z}^* Li^* K ≅ Rc_{1Z!} Li'^* Lc₂^* K ≅ Li^* Rc₁_! Lc₂^* K --Li^* û--> Li^* K,
```
with `û : Rc₁_! Lc₂^* K ⟶ K` the `Rc₁_! ⊣ Rc₁^!` adjoint of `u`. -/
theorem homEquiv_symm_restrictedCoeffOfIsPullback :
    haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
    ((boundedConstructibleUpperShriekAdjunction ℓ c₁Z).homEquiv _ _).symm
        (restrictedCoeffOfIsPullback sq w₂ K u) =
      (boundedConstructibleLowerShriek ℓ c₁Z).map (upperStarIsoOfComm w₂ K).hom ≫
        inv ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).obj K)) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map
          (((boundedConstructibleUpperShriekAdjunction ℓ c₁).homEquiv _ _).symm u) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have n := (asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)).inv.naturality u
  dsimp only [Functor.comp_map, Functor.comp_obj, asIso_inv] at n
  rw [restrictedCoeffOfIsPullback, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, asIso_inv]
  simp only [NatIso.isIso_inv_app] at n
  simp only [reassoc_of% n, Adjunction.homEquiv_counit, Functor.map_comp, NatIso.isIso_inv_app]

/-- Transporting `Lm^* φ` along an equality `m = m'` of morphisms. -/
@[reassoc]
lemma upperStar_map_comp_eqToHom {m m' : CZ ⟶ X} (h : m = m')
    {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : A ⟶ B) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ m).map φ ≫
        eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ m').map φ := by
  subst h
  simp

/-- For `i' ≫ c₂ = c_{2Z} ≫ i`, the composite
```
Li'^* Lc₂^* K --η--> Li'^* Lc₂^* Ri_* Li^* K ≅ Lc_{2Z}^* Li^* Ri_* Li^* K --ε--> Lc_{2Z}^* Li^* K
  ≅ Li'^* Lc₂^* K
```
is the identity, by the triangle identity of `Li^* ⊣ Ri_*`. -/
@[reassoc]
lemma upperStar_map_upperStar_map_unit_comp_counit_comp_eq_id :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i').map
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i' c₂).inv.app
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ≫
      eqToHom (by rw [w₂]) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c₂Z i).hom.app
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂Z).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)) ≫
      (upperStarIsoOfComm w₂ K).hom =
      𝟙 _ := by
  have h₁ := (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i'
    c₂).inv.naturality ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)
  have h₂ := (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c₂Z
    i).hom.naturality ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K)
  have h₃ := (boundedConstructibleUpperStarLowerStarAdjunction ℓ i).left_triangle_components K
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h₁ h₂ h₃
  rw [reassoc_of% h₁, upperStar_map_comp_eqToHom_assoc w₂, reassoc_of% h₂,
    ← Functor.map_comp_assoc, h₃, CategoryTheory.Functor.map_id, Category.id_comp,
    upperStarIsoOfComm, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.hom_inv_id_app_assoc, eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.app_hom, Iso.inv_hom_id_app]
  rfl

end Restriction
namespace Correspondence

-- unfolding the projections of the diagram in the instantiated statement is slow
/-- The double transpose of a composite with the coefficient pushforward of a proper pushforward
diagram `(f, g)` given by its fields, for the adjunctions `Rb₁_! ⊣ Rb₁^!` and `Lf^* ⊣ Rf_*`
(`ProperPushforwardDiagram.map_map_comp_pushforwardCoeff_comp_counit` with the fields of the
diagram made explicit). -/
private lemma map_map_comp_pushforwardCoeff_mk_comp_counit
    {S Y D : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
    {A : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (e : Correspondence ℓ A) (f : S ⟶ Y)
    [IsProper f.left] (b₁ b₂ : D ⟶ Y) (g : e.C ⟶ D) [IsProper g.left] (w₁ : g ≫ b₁ = e.c₁ ≫ f)
    (w₂ : g ≫ b₂ = e.c₂ ≫ f) {T : Dᵇc(D.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : T ⟶ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b₂).obj
      ((boundedConstructibleLowerStar ℓ f).obj A)) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleLowerShriek ℓ b₁).map
            (ψ ≫ (ProperPushforwardDiagram.mk (c := e) f D b₁ b₂ g w₁ w₂).pushforwardCoeff) ≫
          (boundedConstructibleUpperShriekAdjunction ℓ b₁).counit.app
            ((boundedConstructibleLowerStar ℓ f).obj A)) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app A =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleLowerShriek ℓ b₁).map ψ) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleLowerShriek ℓ b₁).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj A)))) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((lowerStarLowerShriekCompIso ℓ w₁).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj A)))) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app
        ((boundedConstructibleLowerShriek ℓ e.c₁).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj A)))) ≫
      (boundedConstructibleLowerShriek ℓ e.c₁).map
        (((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g b₂).inv.app
              ((boundedConstructibleLowerStar ℓ f).obj A) ≫
            eqToHom (by rw [w₂]) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ e.c₂ f).hom.app
              ((boundedConstructibleLowerStar ℓ f).obj A) ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.c₂).map
              ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app A)) ≫ e.u) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ e.c₁).counit.app A :=
  ProperPushforwardDiagram.map_map_comp_pushforwardCoeff_comp_counit
    (.mk (c := e) f D b₁ b₂ g w₁ w₂) ψ

variable {X Z CZ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType CZ.hom] [QuasiCompact CZ.hom] [IsSeparated CZ.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)
  {i : Z ⟶ X} {i' : CZ ⟶ c.C} {c₁Z c₂Z : CZ ⟶ Z}
  (sq : IsPullback i' c₁Z c.c₁ i) (w₂ : i' ≫ c.c₂ = c₂Z ≫ i)

/-- The *restriction* `c_Z = (C_Z, c_{1Z}, c_{2Z}, u_{|Z})` of an endocorrespondence `c` of
`(X, K)` to a closed subscheme `i : Z ⟶ X`, a correspondence of `(Z, Li^* K)` (blueprint
`lemma-closed-piece-pushforward`): its support is `C_Z = c₁⁻¹(Z)` (the square
`i' ≫ c₁ = c_{1Z} ≫ i` is cartesian), on which `c₂` factors through `Z`, and its coefficient map
is the restriction `u_{|Z}` of `u` (`restrictedCoeffOfIsPullback`). -/
noncomputable def restrictClosed :
    Correspondence ℓ ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K)
    where
  C := CZ
  c₁ := c₁Z
  c₂ := c₂Z
  u := restrictedCoeffOfIsPullback sq w₂ K c.u

variable [hi : IsProper i.left]
include hi

/-- The proper pushforward diagram `(i, i')` from the restriction `c_Z` of `c` to a closed
subscheme back to `c`: a diagram since `i' ≫ c₁ = c_{1Z} ≫ i` and `i' ≫ c₂ = c_{2Z} ≫ i`. Its
coefficient pushforward is the *closed piece coefficient* `u_Z = [i, i']_! u_{|Z}` on the closed
piece `K_Z = Ri_* Li^* K` (blueprint `lemma-closed-piece-pushforward`). -/
noncomputable abbrev closedPieceDiagram : (c.restrictClosed sq w₂).ProperPushforwardDiagram X where
  f := i
  D := c.C
  b₁ := c.c₁
  b₂ := c.c₂
  g := i'
  isProper_g := isProper_left_of_isPullback sq
  w₁ := sq.w
  w₂ := w₂

/-- **The closed piece is the pushforward of the restriction** (blueprint
`lemma-closed-piece-pushforward`; Varshavsky, Lemma 1.5.9): for a closed subscheme
`i : Z ⟶ X` with `C_Z = c₁⁻¹(Z)` mapped into `Z` by `c₂`, the closed piece coefficient
`u_Z = [i, i']_! u_{|Z}`, the pushforward of the restriction of `u` to `Z`, is compatible with `u`
along the unit `η : K ⟶ Ri_* Li^* K`: `u_Z ∘ Lc₂^* η = Rc₁^! η ∘ u`, i.e. the square
```
Lc₂^* K --Lc₂^* η--> Lc₂^* K_Z
   |u                    |u_Z
   v                     v
Rc₁^! K --Rc₁^! η--> Rc₁^! K_Z
```
commutes, where `K_Z = Ri_* Li^* K`. -/
theorem upperStar_map_unit_comp_closedPieceCoeff :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) ≫
      (c.closedPieceDiagram sq w₂).pushforwardCoeff =
    c.u ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K) := by
  have := isProper_left_of_isPullback sq
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have h := map_map_comp_pushforwardCoeff_mk_comp_counit (c.restrictClosed sq w₂) i c.c₁ c.c₂ i'
    sq.w w₂
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K))
  dsimp only [restrictClosed] at h
  refine Adjunction.eq_of_map_comp_counit_eq (boundedConstructibleUpperShriekAdjunction ℓ c.c₁)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ i) _ _ ((h.trans ?_).trans
      (Adjunction.map_map_comp_map_unit_comp_counit
        (boundedConstructibleUpperShriekAdjunction ℓ c.c₁)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ i) c.u).symm)
  rw [← boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_eq_assoc ℓ sq]
  have n₁ := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).naturality
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ i).unit.app K))
  dsimp only [Functor.comp_map] at n₁
  rw [reassoc_of% n₁]
  simp only [restrictedCoeffOfIsPullback, Category.assoc]
  rw [← Functor.map_comp_assoc]
  simp only [upperStar_map_upperStar_map_unit_comp_counit_comp_eq_id_assoc w₂ K]
  rw [Adjunction.map_comp_homEquiv_comp_counit]
  have n₂ := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).naturality c.u
  dsimp only [Functor.comp_map] at n₂
  have e := Iso.hom_inv_id_app (asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq))
    ((boundedConstructibleUpperShriek ℓ c.c₁).obj K)
  rw [asIso_hom] at e
  rw [← reassoc_of% n₂, reassoc_of% e, Functor.map_comp]

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
