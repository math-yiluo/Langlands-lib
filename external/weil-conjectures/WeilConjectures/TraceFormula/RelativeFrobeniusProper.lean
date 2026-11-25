/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.RelativeFrobeniusComparison

/-!

# The Frobenius comparison of the lower shriek for proper morphisms

Let `f : X ⟶ Y` be a morphism of separated `k`-schemes of finite type, with endomorphisms
`Φ_X`, `Φ_Y`, a cartesian square `sq : p ≫ f = f' ≫ Φ_Y` and a relative Frobenius `r` with
`r ≫ p = Φ_X` and `r ≫ f' = f`. The Frobenius comparison
`θ_f : Rf_! ⋙ LΦ_Y^* ≅ LΦ_X^* ⋙ Rf_!` is
`ProEtale.CondensedRing.weilLowerShriekFrobeniusComparison` (blueprint
`lemma-comparison-via-relative-frobenius--2`). This file proves that for proper `f`, under the
identification `Rf_! ≅ Rf_*`, it is the direct-image base change `Ex_*` of the commutative square
`Φ_X ≫ f = f ≫ Φ_Y`
(`ProEtale.CondensedRing.weilLowerShriekFrobeniusComparison_hom_app_comp_isoLowerStar`).

The proof identifies `Ex_!` of `sq` with `Ex_*` (`def-exchange-projection`), and the relative
pullback along `r` with the exchange of the triangle `r ≫ f' = f`; the two exchanges then paste
to the exchange of the square `Φ_X ≫ f = f ≫ Φ_Y`
(`CategoryTheory.Adjunction.exchangeRight_app_paste`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B]

/-- **The exchange of a triangle of left adjoints.** For adjunctions `F ⊣ Rf`, `F' ⊣ Rf'`,
`Fr ⊣ Rr` and an isomorphism `cF : F ≅ F' ⋙ Fr`, the exchange morphism `Rf' ⟶ Rf ∘ Fr` of the
triangle is the unit of `Fr ⊣ Rr` followed by the conjugate `Rf' ∘ Rr ⟶ Rf` of `cF`. -/
lemma exchangeRight_leftUnitor_trans_app {F : B ⥤ A} {Rf : A ⥤ B} {F' : B ⥤ A'} {Rf' : A' ⥤ B}
    {Fr : A' ⥤ A} {Rr : A ⥤ A'} (af : F ⊣ Rf) (af' : F' ⊣ Rf') (ar : Fr ⊣ Rr)
    (cF : F ≅ F' ⋙ Fr) (M : A') :
    (exchangeRight af' af (F.leftUnitor ≪≫ cF)).app M =
      Rf'.map (ar.unit.app M) ≫ (conjugateEquiv (af'.comp ar) af cF.hom).app (Fr.obj M) := by
  have hu := unit_conjugateEquiv (af'.comp ar) af cF.hom (Rf'.obj M)
  have hn := (conjugateEquiv (af'.comp ar) af cF.hom).naturality (Fr.map (af'.counit.app M))
  have hr := ar.unit.naturality (af'.counit.app M)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    comp_unit_app] at hu hn hr
  rw [exchangeRight_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Functor.id_obj, Functor.comp_obj]
  rw [← reassoc_of% hu, ← hn, ← Functor.map_comp_assoc, ← hr]
  simp only [Functor.map_comp, Category.assoc, right_triangle_components_assoc]

variable {A'' B' : Type*} [Category* A''] [Category* B']

/-- **Pasting an exchange with the exchange of a triangle.** Let `F ⊣ Rf`, `F' ⊣ Rf'`,
`Fr ⊣ Rr` be adjunctions with `cF : F ≅ F' ⋙ Fr`, and let `θs : GY ⋙ F' ≅ F ⋙ GP` and
`θw : GY ⋙ F ≅ F ⋙ GΦ` be compatible with `cF` through `cΦ : GΦ ≅ GP ⋙ Fr`. Then the exchange
of `θs` followed by the unit of `Fr ⊣ Rr`, the conjugate `Rf' ∘ Rr ⟶ Rf` of `cF` and `cΦ⁻¹` is
the exchange of `θw`. -/
lemma exchangeRight_app_comp_unit_comp_conjugateEquiv {F : B ⥤ A} {Rf : A ⥤ B} {F' : B ⥤ A'}
    {Rf' : A' ⥤ B} {Fr : A' ⥤ A} {Rr : A ⥤ A'} {GY : B ⥤ B} {GP : A ⥤ A'} {GΦ : A ⥤ A}
    (af : F ⊣ Rf) (af' : F' ⊣ Rf') (ar : Fr ⊣ Rr) (cF : F ≅ F' ⋙ Fr)
    (θs : GY ⋙ F' ≅ F ⋙ GP) (θw : GY ⋙ F ≅ F ⋙ GΦ) (cΦ : GΦ ≅ GP ⋙ Fr)
    (h : ∀ N : B, θw.hom.app N ≫ cΦ.hom.app (F.obj N) =
      cF.hom.app (GY.obj N) ≫ Fr.map (θs.hom.app N)) (K : A) :
    (exchangeRight af af' θs).app K ≫ Rf'.map (ar.unit.app (GP.obj K)) ≫
        (conjugateEquiv (af'.comp ar) af cF.hom).app (Fr.obj (GP.obj K)) ≫
        Rf.map (cΦ.inv.app K) =
      (exchangeRight af af θw).app K := by
  have hp := exchangeRight_app_paste af af' af θs (F.leftUnitor ≪≫ cF) θw GY.rightUnitor.symm cΦ
    (fun N ↦ by simpa using (h N).symm) K
  rw [exchangeRight_leftUnitor_trans_app af af' ar] at hp
  simp only [Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.id_obj, Functor.comp_obj,
    Functor.id_map, Category.id_comp] at hp
  rw [reassoc_of% hp, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id, Category.comp_id]

end CategoryTheory.Adjunction

namespace CategoryTheory

/-- The composition isomorphisms of a family of pullback functors are compatible with the
transport along an equation `u = v`. -/
@[reassoc]
lemma comp_hom_app_comp_map_eqToHom {𝒞 : Type*} [Category* 𝒞] {X X' Y : 𝒞}
    {DX DX' DY : Type*} [Category* DX] [Category* DX'] [Category* DY]
    (UXX' : (X ⟶ X') → DX' ⥤ DX) (UX'Y : (X' ⟶ Y) → DY ⥤ DX') (UXY : (X ⟶ Y) → DY ⥤ DX)
    (c : ∀ (a : X ⟶ X') (b : X' ⟶ Y), UXY (a ≫ b) ≅ UX'Y b ⋙ UXX' a) (r : X ⟶ X')
    {u v : X' ⟶ Y} (e : u = v) (N : DY) :
    (c r u).hom.app N ≫ (UXX' r).map (eqToHom (by rw [e])) =
      eqToHom (by rw [e]) ≫ (c r v).hom.app N := by
  subst e
  simp

/-- An abstract coherence of composition isomorphisms of families of pullback functors, used to
compare the pullback comparisons of the squares `p ≫ (r ≫ f') = f' ≫ Φ_Y` and
`(r ≫ p) ≫ (r ≫ f') = (r ≫ f') ≫ Φ_Y`: the hypotheses `H₁`, `H₂` are instances of the
associativity of the composition isomorphisms. Stating it for abstract families keeps the
computation cheap. -/
lemma pullbackComparison_hom_app_comp_hom_app_coherence {𝒞 : Type*} [Category* 𝒞]
    {X X' Y : 𝒞} {DX DX' DY : Type*} [Category* DX] [Category* DX'] [Category* DY]
    (UXX' : (X ⟶ X') → DX' ⥤ DX) (UX'X : (X' ⟶ X) → DX ⥤ DX') (UX'Y : (X' ⟶ Y) → DY ⥤ DX')
    (UXY : (X ⟶ Y) → DY ⥤ DX) (UYY : (Y ⟶ Y) → DY ⥤ DY) (UXX : (X ⟶ X) → DX ⥤ DX)
    (cXX'Y : ∀ (a : X ⟶ X') (b : X' ⟶ Y), UXY (a ≫ b) ≅ UX'Y b ⋙ UXX' a)
    (cXYY : ∀ (a : X ⟶ Y) (b : Y ⟶ Y), UXY (a ≫ b) ≅ UYY b ⋙ UXY a)
    (cX'YY : ∀ (a : X' ⟶ Y) (b : Y ⟶ Y), UX'Y (a ≫ b) ≅ UYY b ⋙ UX'Y a)
    (cXXY : ∀ (a : X ⟶ X) (b : X ⟶ Y), UXY (a ≫ b) ≅ UXY b ⋙ UXX a)
    (cX'XY : ∀ (a : X' ⟶ X) (b : X ⟶ Y), UX'Y (a ≫ b) ≅ UXY b ⋙ UX'X a)
    (cXX'X : ∀ (a : X ⟶ X') (b : X' ⟶ X), UXX (a ≫ b) ≅ UX'X b ⋙ UXX' a)
    (H₁ : ∀ (a : X ⟶ X') (b : X' ⟶ X) (g : X ⟶ Y) (N : DY),
      (cXXY (a ≫ b) g).hom.app N ≫ (cXX'X a b).hom.app ((UXY g).obj N) =
        eqToHom (by rw [Category.assoc]) ≫ (cXX'Y a (b ≫ g)).hom.app N ≫
          (UXX' a).map ((cX'XY b g).hom.app N))
    (H₂ : ∀ (a : X ⟶ X') (b : X' ⟶ Y) (g : Y ⟶ Y) (N : DY),
      (cXYY (a ≫ b) g).hom.app N ≫ (cXX'Y a b).hom.app ((UYY g).obj N) =
        eqToHom (by rw [Category.assoc]) ≫ (cXX'Y a (b ≫ g)).hom.app N ≫
          (UXX' a).map ((cX'YY b g).hom.app N))
    (r : X ⟶ X') (p : X' ⟶ X) (f' : X' ⟶ Y) (ΦY : Y ⟶ Y) (w : p ≫ r ≫ f' = f' ≫ ΦY)
    (w' : (r ≫ p) ≫ r ≫ f' = (r ≫ f') ≫ ΦY) (N : DY) :
    ((cXYY (r ≫ f') ΦY).inv.app N ≫ eqToHom (by rw [w']) ≫ (cXXY (r ≫ p) (r ≫ f')).hom.app N) ≫
        (cXX'X r p).hom.app ((UXY (r ≫ f')).obj N) =
      (cXX'Y r f').hom.app ((UYY ΦY).obj N) ≫
        (UXX' r).map ((cX'YY f' ΦY).inv.app N ≫ eqToHom (by rw [w]) ≫
          (cX'XY p (r ≫ f')).hom.app N) := by
  have H₂' : (cXX'Y r f').hom.app ((UYY ΦY).obj N) ≫ (UXX' r).map ((cX'YY f' ΦY).inv.app N) =
      (cXYY (r ≫ f') ΦY).inv.app N ≫ eqToHom (by rw [Category.assoc]) ≫
        (cXX'Y r (f' ≫ ΦY)).hom.app N := by
    rw [← cancel_epi ((cXYY (r ≫ f') ΦY).hom.app N), reassoc_of% (H₂ r f' ΦY N),
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
      Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [H₁, reassoc_of% H₂', comp_hom_app_comp_map_eqToHom_assoc UXX' UX'Y UXY cXX'Y r w.symm]
  simp

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Proper

variable {X X' Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The pullback comparison of the square `(r ≫ p) ≫ (r ≫ f') = (r ≫ f') ≫ Φ_Y` is the
pullback along `r` of the pullback comparison of the square `p ≫ (r ≫ f') = f' ≫ Φ_Y`, through
the composition isomorphisms `L(r ≫ p)^* ≅ Lp^* ⋙ Lr^*` and `L(r ≫ f')^* ≅ Lf'^* ⋙ Lr^*`. -/
lemma boundedConstructiblePullbackSquareComparison_hom_app_comp_upperStarComp (r : X ⟶ X')
    (p : X' ⟶ X) (f' : X' ⟶ Y) (ΦY : Y ⟶ Y) (w : CommSq p f' (r ≫ f') ΦY)
    (w' : CommSq (r ≫ p) (r ≫ f') (r ≫ f') ΦY)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ w').hom.app
        N ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ f')).obj N) =
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r f').hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦY).obj N) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).map
        ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
          w).hom.app N) := by
  rw [boundedConstructiblePullbackSquareComparison_hom_app,
    boundedConstructiblePullbackSquareComparison_hom_app]
  exact pullbackComparison_hom_app_comp_hom_app_coherence
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b g N ↦
      boundedConstructibleUpperStarComp_assoc_app (Profinite.padicAlgClRingObj ℓ) ℓ a b g N)
    (fun a b g N ↦
      boundedConstructibleUpperStarComp_assoc_app (Profinite.padicAlgClRingObj ℓ) ℓ a b g N)
    r p f' ΦY w.w w'.w N

/-- The composition isomorphism `Rr_* ⋙ Rf'_* ≅ R(r ≫ f')_*` is the conjugate of the composition
isomorphism `L(r ≫ f')^* ≅ Lf'^* ⋙ Lr^*` of the pullbacks. -/
lemma boundedConstructibleLowerStarComp_hom (r : X ⟶ X') (f' : X' ⟶ Y) :
    (boundedConstructibleLowerStarComp ℓ r f').hom =
      conjugateEquiv
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
          f').comp
          (boundedConstructibleUpperStarLowerStarAdjunction ℓ r))
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ
          (r ≫ f'))
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r f').hom :=
  rfl

/-- **The relative pullback for proper maps** is the exchange of the triangle `r ≫ f'`: under the
identifications `Rf'_! ≅ Rf'_*` and `R(r ≫ f')_! ≅ R(r ≫ f')_*`, it is
`Rf'_* M ⟶ Rf'_* Rr_* Lr^* M ≅ R(r ≫ f')_* Lr^* M`. -/
@[reassoc]
lemma relativePullback_app_comp_isoLowerStar (r : X ⟶ X') (f' : X' ⟶ Y) [IsProper r.left]
    [IsProper f'.left] [IsProper (r ≫ f').left]
    (M : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (relativePullback ℓ r f' (r ≫ f') rfl).app M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (r ≫ f')).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M) =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f').hom.app M ≫
        (boundedConstructibleLowerStar ℓ f').map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            r).unit.app M) ≫
        (boundedConstructibleLowerStarComp ℓ r f').hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M) := by
  have hc := boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ r f'
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)
  have hc' : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (r ≫ f')).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M) =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f').hom.app _ ≫
        (boundedConstructibleLowerStar ℓ f').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).hom.app _) ≫
        (boundedConstructibleLowerStarComp ℓ r f').hom.app _ := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').hom.app _),
      Iso.hom_inv_id_app_assoc, reassoc_of% hc, Iso.inv_hom_id_app, Category.comp_id]
  rw [relativePullback_app]
  simp only [eqToHom_refl, Category.comp_id, Category.assoc]
  rw [hc', ← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rfl

end Proper

section LowerShriek

variable {X Y X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (f : X ⟶ Y) {p : X' ⟶ X} {f' : X' ⟶ Y}
  (sq : IsPullback p f' f ΦY) (r : X ⟶ X') (hrp : r ≫ p = ΦX) (hrf : r ≫ f' = f)
  [IsFinite r.left] [IsUniversalHomeomorphism r.left]

/-- The Frobenius comparison of the lower shriek of a proper morphism is the direct-image base
change of the commutative square `Φ_X ≫ f = f ≫ Φ_Y`, for any proof `W` of its commutativity. -/
theorem weilLowerShriekFrobeniusComparison_hom_app_comp_isoLowerStar_of_commSq [IsProper f.left]
    (W : CommSq ΦX f f ΦY) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf).hom.app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦY).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K) ≫
        (boundedConstructibleBaseChange ℓ W).app K := by
  have : IsProper f'.left := MorphismProperty.of_isPullback sq.overLeft inferInstance
  rw [weilLowerShriekFrobeniusComparison_hom_app_eq]
  subst hrp hrf
  simp only [eqToHom_refl, Category.comp_id, Category.assoc]
  rw [(boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (r ≫ f')).hom.naturality,
    relativePullback_app_comp_isoLowerStar_assoc,
    reassoc_of% (boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper ℓ sq K)]
  refine congrArg (_ ≫ ·) ?_
  rw [boundedConstructibleBaseChange_eq_exchangeRight,
    boundedConstructibleBaseChange_eq_exchangeRight, boundedConstructibleLowerStarComp_hom]
  exact Adjunction.exchangeRight_app_comp_unit_comp_conjugateEquiv
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (r ≫ f'))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f')
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ r)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r f')
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq)
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ W)
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p)
    (fun N ↦ boundedConstructiblePullbackSquareComparison_hom_app_comp_upperStarComp ℓ r p f' ΦY
      sq.toCommSq W N) K

/-- **The Frobenius comparison of the lower shriek of a proper morphism is the direct-image base
change** (blueprint `lemma-comparison-via-relative-frobenius--2`, `def-exchange-projection`): for
proper `f`, under the identification `Rf_! ≅ Rf_*`, the Frobenius comparison
`θ_f : LΦ_Y^* Rf_! ≅ Rf_! LΦ_X^*` is the base-change morphism `Ex_* : LΦ_Y^* Rf_* ⟶ Rf_* LΦ_X^*` of
the commutative square `Φ_X ≫ f = f ≫ Φ_Y`. -/
theorem weilLowerShriekFrobeniusComparison_hom_app_comp_isoLowerStar [IsProper f.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf).hom.app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦY).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K) ≫
        (boundedConstructibleBaseChange ℓ
          (⟨frobenius_comp_eq_comp_frobenius ΦX ΦY f sq r hrp hrf⟩ : CommSq ΦX f f ΦY)).app K :=
  weilLowerShriekFrobeniusComparison_hom_app_comp_isoLowerStar_of_commSq ℓ ΦX ΦY f sq r hrp hrf _ K

end LowerShriek

end AlgebraicGeometry.ProEtale.CondensedRing
