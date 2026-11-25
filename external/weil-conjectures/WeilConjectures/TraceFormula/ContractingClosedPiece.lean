/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.ClosedPieceSquare
public import WeilConjectures.TraceFormula.LocalTermLocality

/-!

# The closed piece coefficient of a correspondence at a point with reduced fibre

Let `c = (c₁, c₂)` be an endocorrespondence of `(X, K)` with coefficient map
`u : Lc₂^* K ⟶ Rc₁^! K`, and `y` a `k`-point of `C` on the fixed locus whose fibre
`c₁⁻¹(x)`, `x = c₁(y)`, is the reduced point `y`. The closed piece coefficient
`u^Z = [x, y]_! u_Z` on `K^Z = Rx_* Lx^* K` (the coefficient pushforward of the restricted
coefficient map `u_Z` along `Correspondence.restrictedClosedPieceDiagram`) is compatible with `u`
along the unit `η : K ⟶ Rx_* Lx^* K` (blueprint `proposition-additivity-trace-classes--2`, proof of
item 1, step (b)):
```
u^Z ∘ Lc₂^* η = Rc₁^! η ∘ u,
```
`Correspondence.upperStar_map_unit_comp_restrictedClosedPieceCoeff`.

Both sides are compared after the injective double transposition along `Rc₁_! ⊣ Rc₁^!` and
`Lx^* ⊣ Rx_*`. The key input is the description of the compact-support base change `Ex_!` of the
cartesian square `y ≫ c₁ = 𝟙 ≫ x` through the units and counits of the ordinary adjunctions
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_eq`), a
consequence of the mate description of `Ex_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv`,
blueprint `proposition-composition-base-change-rf-shriek`, clause (4)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section Abstract

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ R₁' : D ⥤ C} {L₂ : E ⥤ F} {R₂ R₂' : F ⥤ E}

/-- The inverse mate for adjunctions transported along isomorphisms of the right adjoints. -/
lemma mateEquiv_ofNatIsoRight_symm_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : R₁ ≅ R₁')
    (e₂ : R₂ ≅ R₂') (α : TwoSquare R₁' H G R₂') (c : C) :
    ((mateEquiv (adj₁.ofNatIsoRight e₁) (adj₂.ofNatIsoRight e₂)).symm α).app c =
      L₂.map (G.map (adj₁.unit.app c)) ≫ L₂.map (G.map (e₁.hom.app (L₁.obj c))) ≫
        L₂.map (α.app (L₁.obj c)) ≫ L₂.map (e₂.inv.app (H.obj (L₁.obj c))) ≫
        adj₂.counit.app (H.obj (L₁.obj c)) := by
  simp [mateEquiv, Adjunction.ofNatIsoRight]

end Abstract

namespace Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- Two maps into `U (Q A)` agree if their double transposes for `S ⊣ U` and `P ⊣ Q` agree. -/
lemma eq_of_map_comp_counit_eq {S : C ⥤ D} {U : D ⥤ C} {P : D ⥤ E} {Q : E ⥤ D}
    (adjS : S ⊣ U) (adjP : P ⊣ Q) {T : C} {A : E} (φ₁ φ₂ : T ⟶ U.obj (Q.obj A))
    (h : P.map (S.map φ₁ ≫ adjS.counit.app _) ≫ adjP.counit.app A =
      P.map (S.map φ₂ ≫ adjS.counit.app _) ≫ adjP.counit.app A) : φ₁ = φ₂ := by
  apply (adjS.homEquiv _ _).symm.injective
  apply (adjP.homEquiv _ _).symm.injective
  simpa only [homEquiv_counit] using h

/-- The double transpose of `u ≫ U η`. -/
lemma map_map_comp_map_unit_comp_counit {S : C ⥤ D} {U : D ⥤ C} {P : D ⥤ E} {Q : E ⥤ D}
    (adjS : S ⊣ U) (adjP : P ⊣ Q) {T : C} {B : D} (v : T ⟶ U.obj B) :
    P.map (S.map (v ≫ U.map (adjP.unit.app B)) ≫ adjS.counit.app _) ≫
        adjP.counit.app (P.obj B) =
      P.map (S.map v ≫ adjS.counit.app B) := by
  simp

/-- The left adjunct of a composite with a right adjunct. -/
lemma map_comp_homEquiv_comp_counit {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {T T' : C} {B : D}
    (a : T ⟶ T') (θ : F.obj T' ⟶ B) :
    F.map (a ≫ adj.homEquiv _ _ θ) ≫ adj.counit.app B = F.map a ≫ θ := by
  simp [homEquiv_unit]

/-- The double transpose of a coefficient pushforward: for adjunctions `Lg ⊣ Rg`, `Lf ⊣ Rf`,
`B_! ⊣ B^!`, `C_! ⊣ C^!` and a 2-square `Ξ : Rg ⋙ B_! ⟶ C_! ⋙ Rf`, the composite
```
Lf B_! T --ψ, η, Rg a, Rg u, mate Ξ--> Lf B_! B^! Rf A --ε--> Lf Rf A --ε--> A
```
is `Lf B_! ψ ≫ Lf B_! η ≫ Lf Ξ ≫ ε ≫ C_! (a ≫ u) ≫ ε`. -/
lemma map_map_comp_mateEquiv_app_comp_counit {𝒞 𝒟 𝒮 𝒴 : Type*} [Category* 𝒞] [Category* 𝒟]
    [Category* 𝒮] [Category* 𝒴] {Lg : 𝒟 ⥤ 𝒞} {Rg : 𝒞 ⥤ 𝒟} {Lf : 𝒴 ⥤ 𝒮} {Rf : 𝒮 ⥤ 𝒴}
    {B₁ : 𝒟 ⥤ 𝒴} {B₂ : 𝒴 ⥤ 𝒟} {C₁ : 𝒞 ⥤ 𝒮} {C₂ : 𝒮 ⥤ 𝒞} (adjG : Lg ⊣ Rg) (adjF : Lf ⊣ Rf)
    (adjB : B₁ ⊣ B₂) (adjC : C₁ ⊣ C₂) (Ξ : TwoSquare Rg C₁ B₁ Rf) {T N : 𝒟} {M : 𝒞} {A : 𝒮}
    (ψ : T ⟶ N) (a : Lg.obj N ⟶ M) (u : M ⟶ C₂.obj A) :
    Lf.map (B₁.map (ψ ≫ (adjG.unit.app N ≫ Rg.map a) ≫ Rg.map u ≫
        (mateEquiv adjC adjB Ξ).app A) ≫ adjB.counit.app (Rf.obj A)) ≫ adjF.counit.app A =
      Lf.map (B₁.map ψ) ≫ Lf.map (B₁.map (adjG.unit.app N)) ≫ Lf.map (Ξ.app (Lg.obj N)) ≫
        adjF.counit.app _ ≫ C₁.map (a ≫ u) ≫ adjC.counit.app A := by
  have n₁ := Ξ.naturality (a ≫ u)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at n₁
  simp only [Functor.map_comp, Category.assoc, mateEquiv_counit, reassoc_of% n₁]
  simp

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section BaseChange

variable (ℓ) {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **`Ex_!` through the units and counits of the ordinary adjunctions**: for a cartesian square
`g' ≫ f = f' ≫ g` with proper horizontal maps, `Ex_!` at `N` is
```
Lg^* Rf_! N --η--> Lg^* Rf_! Rg'_* Lg'^* N --Ξ--> Lg^* Rg_* Rf'_! Lg'^* N --ε--> Rf'_! Lg'^* N,
```
with `Ξ` the composition isomorphism `lowerStarLowerShriekCompIso`. -/
@[reassoc]
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_eq (sq : IsPullback g' f' f g)
    [IsProper g.left] [IsProper g'.left] (w : g' ≫ f = f' ≫ g)
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app N =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((boundedConstructibleLowerShriek ℓ f).map
            ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g').unit.app N)) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((lowerStarLowerShriekCompIso ℓ w).hom.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj N)) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ g).counit.app
          ((boundedConstructibleLowerShriek ℓ f').obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj N)) := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv,
    boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    mateEquiv_ofNatIsoRight_symm_app]
  simp only [lowerStarLowerShriekCompIso, boundedConstructibleLowerShriekSquareIso_padicAlgCl,
    Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]

end BaseChange

section Unit

variable {T C X : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
  [IsSeparated T.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- For `x = y ≫ c₂`, the composite
```
Ly^* Lc₂^* K --η--> Ly^* Lc₂^* Rx_* Lx^* K ≅ L(𝟙)^* Lx^* Rx_* Lx^* K --ε--> L(𝟙)^* Lx^* K
  ≅ Lx^* K ≅ Ly^* Lc₂^* K
```
is the identity, by the triangle identity of `Lx^* ⊣ Rx_*`. -/
@[reassoc]
lemma upperStar_map_upperStar_map_unit_comp_counit_eq_id (y : T ⟶ C) (c₂ : C ⟶ X) (x : T ⟶ X)
    (hx : x = y ≫ c₂) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c₂).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).unit.app K)) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ y c₂).inv.app
        ((boundedConstructibleLowerStar ℓ x).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) ≫
      eqToHom (by rw [hx, Category.id_comp]) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 T) x).hom.app
        ((boundedConstructibleLowerStar ℓ x).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 T)).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ x).counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) ≫
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ T).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K) ≫
      eqToHom (by rw [hx] :
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K =
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (y ≫ c₂)).obj K) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ y c₂).hom.app K =
      𝟙 _ := by
  subst hx
  have h₁ := (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ y
    c₂).inv.naturality ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (y ≫ c₂)).unit.app K)
  have h₂ := (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ T).hom.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (y ≫ c₂)).counit.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (y ≫ c₂)).obj K))
  have h₃ := boundedConstructibleUpperStarComp_id_left_app (Profinite.padicAlgClRingObj ℓ) ℓ
    (y ≫ c₂) ((boundedConstructibleLowerStar ℓ (y ≫ c₂)).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (y ≫ c₂)).obj K))
  have h₄ :=
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (y ≫ c₂)).left_triangle_components K
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂
  dsimp only [Functor.id_obj]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, reassoc_of% h₄, eqToHom_refl, Category.id_comp, Iso.inv_hom_id_app]
  rfl

end Unit

namespace Correspondence

-- matching the per-ring adjunctions against the generic mate lemma unfolds the pullbacks
/-- The double transpose of a composite with the coefficient pushforward of a proper pushforward
diagram, for the adjunctions `Rb₁_! ⊣ Rb₁^!` and `Lf^* ⊣ Rf_*`. -/
lemma ProperPushforwardDiagram.map_map_comp_pushforwardCoeff_comp_counit
    {S Y : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {A : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ A}
    (P : c.ProperPushforwardDiagram Y) {T : Dᵇc(P.D.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : T ⟶ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.b₂).obj P.coeff) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.f).map
        ((boundedConstructibleLowerShriek ℓ P.b₁).map
            (ψ ≫ P.pushforwardCoeff) ≫
          (boundedConstructibleUpperShriekAdjunction ℓ P.b₁).counit.app P.coeff) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ P.f).counit.app A =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.f).map
        ((boundedConstructibleLowerShriek ℓ P.b₁).map ψ) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.f).map
        ((boundedConstructibleLowerShriek ℓ P.b₁).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g).unit.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.b₂).obj
              P.coeff))) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.f).map
        ((lowerStarLowerShriekCompIso ℓ P.w₁).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.g).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.b₂).obj
              P.coeff))) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ P.f).counit.app
        ((boundedConstructibleLowerShriek ℓ c.c₁).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.g).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.b₂).obj
              P.coeff))) ≫
      (boundedConstructibleLowerShriek ℓ c.c₁).map
        (((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ P.g P.b₂).inv.app
              P.coeff ≫
            eqToHom (by rw [P.w₂]) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂ P.f).hom.app
              P.coeff ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
              ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
                P.f).counit.app A)) ≫ c.u) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ c.c₁).counit.app A :=
  Adjunction.map_map_comp_mateEquiv_app_comp_counit
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ P.f)
    (boundedConstructibleUpperShriekAdjunction ℓ P.b₁)
    (boundedConstructibleUpperShriekAdjunction ℓ c.c₁) (lowerStarLowerShriekCompIso ℓ P.w₁).hom
    ψ ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ P.g P.b₂).inv.app
              P.coeff ≫
            eqToHom (by rw [P.w₂]) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂ P.f).hom.app
              P.coeff ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
              ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
                P.f).counit.app A)) c.u

-- unfolding the diagonal correspondence `ofEnd` in the instantiated statement is slow
/-- The double transpose of a composite with the coefficient pushforward of a proper pushforward
diagram `(f, g)` out of the diagonal correspondence of `v`, for the adjunctions
`Rb₁_! ⊣ Rb₁^!` and `Lf^* ⊣ Rf_*`. -/
lemma ProperPushforwardDiagram.map_map_comp_pushforwardCoeff_ofEnd_comp_counit
    {S Y D : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
    {A : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (v : A ⟶ A) (f : S ⟶ Y) [IsProper f.left]
    (b₁ b₂ : D ⟶ Y) (g : S ⟶ D) [IsProper g.left] (w₁ : g ≫ b₁ = 𝟙 S ≫ f)
    (w₂ : g ≫ b₂ = 𝟙 S ≫ f) {T : Dᵇc(D.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : T ⟶ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b₂).obj
      ((boundedConstructibleLowerStar ℓ f).obj A)) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        ((boundedConstructibleLowerShriek ℓ b₁).map
            (ψ ≫ (ProperPushforwardDiagram.mk (c := ofEnd A v) f D b₁ b₂ g w₁
              w₂).pushforwardCoeff) ≫
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
        ((boundedConstructibleLowerShriek ℓ (𝟙 S)).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ b₂).obj
              ((boundedConstructibleLowerStar ℓ f).obj A)))) ≫
      (boundedConstructibleLowerShriek ℓ (𝟙 S)).map
        (((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g b₂).inv.app
              ((boundedConstructibleLowerStar ℓ f).obj A) ≫
            eqToHom (by rw [w₂]) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 S) f).hom.app
              ((boundedConstructibleLowerStar ℓ f).obj A) ≫
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 S)).map
              ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
                f).counit.app A)) ≫
          (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ S).hom.app A ≫ v ≫
          (boundedConstructibleUpperShriekId ℓ S).inv.app A) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ (𝟙 S)).counit.app A :=
  map_map_comp_pushforwardCoeff_comp_counit (.mk (c := ofEnd A v) f D b₁ b₂ g w₁ w₂) ψ

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}

/-- **The closed piece coefficient is compatible with the unit** (blueprint
`proposition-additivity-trace-classes--2`, proof of item 1, step (b), for `Z = {x}`): for a
`k`-point `y` of the fixed locus with reduced fibre `c₁⁻¹(x) = {y}`, `x = c₁(y)`, the closed piece
coefficient `u^Z = [x, y]_! u_Z` satisfies `u^Z ∘ Lc₂^* η = Rc₁^! η ∘ u` for the unit
`η : K ⟶ Rx_* Lx^* K`. -/
theorem upperStar_map_unit_comp_restrictedClosedPieceCoeff {y : RationalPoint c.C}
    (hy : y ≫ c.c₁ = y ≫ c.c₂) (sq : IsPullback y (𝟙 (point k)) c.c₁ (y ≫ c.c₁)) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (y ≫ c.c₁)).unit.app K) ≫
      (restrictedClosedPieceDiagram hy sq).pushforwardCoeff =
    c.u ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (y ≫ c.c₁)).unit.app K) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq
  have h := ProperPushforwardDiagram.map_map_comp_pushforwardCoeff_ofEnd_comp_counit
    (restrictedStalkMap hy sq) (y ≫ c.c₁) c.c₁ c.c₂ y (Category.id_comp _).symm
    (hy.symm.trans (Category.id_comp _).symm)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (y ≫ c.c₁)).unit.app K))
  refine Adjunction.eq_of_map_comp_counit_eq (boundedConstructibleUpperShriekAdjunction ℓ c.c₁)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (y ≫ c.c₁)) _ _ ((h.trans ?_).trans
      (Adjunction.map_map_comp_map_unit_comp_counit
        (boundedConstructibleUpperShriekAdjunction ℓ c.c₁)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ (y ≫ c.c₁)) c.u).symm)
  rw [← boundedConstructibleLowerShriekBaseChange_padicAlgCl_app_eq_assoc ℓ sq]
  have n₁ := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).naturality
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (y ≫ c.c₁)).unit.app K))
  dsimp only [Functor.comp_map] at n₁
  rw [reassoc_of% n₁, restrictedStalkMap]
  simp only [Category.assoc, Functor.id_obj, Iso.hom_inv_id_app, Category.comp_id]
  rw [← Functor.map_comp_assoc,
    upperStar_map_upperStar_map_unit_comp_counit_eq_id_assoc y c.c₂ (y ≫ c.c₁) hy,
    Adjunction.map_comp_homEquiv_comp_counit]
  have n₂ := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).naturality c.u
  dsimp only [Functor.comp_map] at n₂
  have e := Iso.hom_inv_id_app (asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq))
    ((boundedConstructibleUpperShriek ℓ c.c₁).obj K)
  rw [asIso_hom] at e
  rw [← reassoc_of% n₂, reassoc_of% e, Functor.map_comp]

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
