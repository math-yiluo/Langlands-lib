/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp

/-!
# Coherence of the derived (Pull) isomorphism with composition

This file proves that the conjugates `Adjunction.pullIsoOfComapIso` are compatible with the
composition of the vertical adjunctions, provided the isomorphisms they are conjugate to are
(`CategoryTheory.Adjunction.pullIsoOfComapIso_hom_app_comp`). Applied to the derived (Pull)
isomorphism, this reduces its coherence with the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` to the coherence of `derivedComapLowerStarIso` with the composition
isomorphisms `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`
(`ProEtale.CondensedRing.derivedPullIso_hom_app_comp_of_derivedComapLowerStarIso`).

It also contains two abstract tools for the latter:
* `CategoryTheory.Adjunction.conjugateEquiv_comp_app_fac`: the conjugate of a composition
  isomorphism of "derived" left adjoints, read through the comparisons `β`;
* `CategoryTheory.Adjunction.comp_coherence_app_of_isIso`: a diagram chase deducing a coherence
  of "derived" isomorphisms from its "underived" analogue.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- The conjugate of the inverse of an associator is the inverse of an associator. -/
lemma conjugateEquiv_associator_inv
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv := by
  rw [← cancel_mono (Functor.associator R₃₂ R₂₁ R₁₀).hom, Iso.inv_hom_id,
    ← conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃, conjugateEquiv_comp, Iso.hom_inv_id,
    conjugateEquiv_id]

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

variable {A_X A_Y A_Z B_X B_Y B_Z : Type*} [Category* A_X] [Category* A_Y] [Category* A_Z]
  [Category* B_X] [Category* B_Y] [Category* B_Z]
  {E_X : A_X ⥤ B_X} {Res_X : B_X ⥤ A_X} (adj_X : E_X ⊣ Res_X)
  {E_Y : A_Y ⥤ B_Y} {Res_Y : B_Y ⥤ A_Y} (adj_Y : E_Y ⊣ Res_Y)
  {E_Z : A_Z ⥤ B_Z} {Res_Z : B_Z ⥤ A_Z} (adj_Z : E_Z ⊣ Res_Z)
  {U_f : A_Y ⥤ A_X} {L_f : A_X ⥤ A_Y} (adj_f : U_f ⊣ L_f)
  {U_g : A_Z ⥤ A_Y} {L_g : A_Y ⥤ A_Z} (adj_g : U_g ⊣ L_g)
  {U_fg : A_Z ⥤ A_X} {L_fg : A_X ⥤ A_Z} (adj_fg : U_fg ⊣ L_fg)
  {V_f : B_Y ⥤ B_X} {M_f : B_X ⥤ B_Y} (adj'_f : V_f ⊣ M_f)
  {V_g : B_Z ⥤ B_Y} {M_g : B_Y ⥤ B_Z} (adj'_g : V_g ⊣ M_g)
  {V_fg : B_Z ⥤ B_X} {M_fg : B_X ⥤ B_Z} (adj'_fg : V_fg ⊣ M_fg)

/-- The conjugates `Adjunction.pullIsoOfComapIso` of isomorphisms `e_f`, `e_g`, `e_fg`
between composites of right adjoints are compatible with isomorphisms `c : U_fg ≅ U_g ⋙ U_f`
and `c' : V_fg ≅ V_g ⋙ V_f` of left adjoints, as soon as `e_fg` is compatible with `e_f`, `e_g`
and the conjugates of `c` and `c'`. -/
lemma pullIsoOfComapIso_hom_app_comp (c : U_fg ≅ U_g ⋙ U_f) (c' : V_fg ≅ V_g ⋙ V_f)
    (e_f : M_f ⋙ Res_Y ≅ Res_X ⋙ L_f) (e_g : M_g ⋙ Res_Z ≅ Res_Y ⋙ L_g)
    (e_fg : M_fg ⋙ Res_Z ≅ Res_X ⋙ L_fg)
    (h : ∀ N : B_X,
      Res_Z.map ((conjugateIsoEquiv (adj'_g.comp adj'_f) adj'_fg c').hom.app N) ≫
          e_fg.hom.app N =
        e_g.hom.app (M_f.obj N) ≫ L_g.map (e_f.hom.app N) ≫
          (conjugateIsoEquiv (adj_g.comp adj_f) adj_fg c).hom.app (Res_X.obj N))
    (M : A_Z) :
    (pullIsoOfComapIso adj_X adj_Z adj_fg adj'_fg e_fg).hom.app M ≫ c'.hom.app (E_Z.obj M) =
      E_X.map (c.hom.app M) ≫
        (pullIsoOfComapIso adj_X adj_Y adj_f adj'_f e_f).hom.app (U_g.obj M) ≫
          V_f.map ((pullIsoOfComapIso adj_Y adj_Z adj_g adj'_g e_g).hom.app M) := by
  have h₁ : (pullIsoOfComapIso adj_X adj_Z adj_fg adj'_fg e_fg).hom =
      (conjugateEquiv (adj_Z.comp adj'_fg) (adj_fg.comp adj_X)).symm e_fg.hom := rfl
  have h₂ : Functor.whiskerLeft E_Z c'.hom =
      (conjugateEquiv (adj_Z.comp (adj'_g.comp adj'_f)) (adj_Z.comp adj'_fg)).symm
        (Functor.whiskerRight (conjugateIsoEquiv (adj'_g.comp adj'_f) adj'_fg c').hom Res_Z) := by
    rw [Equiv.eq_symm_apply, conjugateEquiv_whiskerLeft]
    rfl
  have h₃ : Functor.whiskerRight c.hom E_X =
      (conjugateEquiv ((adj_g.comp adj_f).comp adj_X) (adj_fg.comp adj_X)).symm
        (Functor.whiskerLeft Res_X (conjugateIsoEquiv (adj_g.comp adj_f) adj_fg c).hom) := by
    rw [Equiv.eq_symm_apply, conjugateEquiv_whiskerRight]
    rfl
  have h₄ : (Functor.associator U_g U_f E_X).hom =
      (conjugateEquiv (adj_g.comp (adj_f.comp adj_X)) ((adj_g.comp adj_f).comp adj_X)).symm
        (Functor.associator _ _ _).hom := by
    rw [Equiv.eq_symm_apply, conjugateEquiv_associator_hom]
  have h₅ : Functor.whiskerLeft U_g (pullIsoOfComapIso adj_X adj_Y adj_f adj'_f e_f).hom =
      (conjugateEquiv (adj_g.comp (adj_Y.comp adj'_f)) (adj_g.comp (adj_f.comp adj_X))).symm
        (Functor.whiskerRight e_f.hom L_g) := by
    rw [Equiv.eq_symm_apply, conjugateEquiv_whiskerLeft]
    exact congrArg (Functor.whiskerRight · L_g)
      ((conjugateEquiv (adj_Y.comp adj'_f) (adj_f.comp adj_X)).apply_symm_apply e_f.hom)
  have h₆ : (Functor.associator U_g E_Y V_f).inv =
      (conjugateEquiv ((adj_g.comp adj_Y).comp adj'_f) (adj_g.comp (adj_Y.comp adj'_f))).symm
        (Functor.associator _ _ _).inv := by
    rw [Equiv.eq_symm_apply, conjugateEquiv_associator_inv]
  have h₇ : Functor.whiskerRight (pullIsoOfComapIso adj_Y adj_Z adj_g adj'_g e_g).hom V_f =
      (conjugateEquiv ((adj_Z.comp adj'_g).comp adj'_f) ((adj_g.comp adj_Y).comp adj'_f)).symm
        (Functor.whiskerLeft M_f e_g.hom) := by
    rw [Equiv.eq_symm_apply, conjugateEquiv_whiskerRight]
    exact congrArg (Functor.whiskerLeft M_f)
      ((conjugateEquiv (adj_Z.comp adj'_g) (adj_g.comp adj_Y)).apply_symm_apply e_g.hom)
  have h₈ : (Functor.associator E_Z V_g V_f).hom =
      (conjugateEquiv (adj_Z.comp (adj'_g.comp adj'_f)) ((adj_Z.comp adj'_g).comp adj'_f)).symm
        (Functor.associator _ _ _).hom := by
    rw [Equiv.eq_symm_apply, conjugateEquiv_associator_hom]
  have key : (pullIsoOfComapIso adj_X adj_Z adj_fg adj'_fg e_fg).hom ≫
      Functor.whiskerLeft E_Z c'.hom =
      Functor.whiskerRight c.hom E_X ≫ (Functor.associator U_g U_f E_X).hom ≫
        Functor.whiskerLeft U_g (pullIsoOfComapIso adj_X adj_Y adj_f adj'_f e_f).hom ≫
        (Functor.associator U_g E_Y V_f).inv ≫
        Functor.whiskerRight (pullIsoOfComapIso adj_Y adj_Z adj_g adj'_g e_g).hom V_f ≫
        (Functor.associator E_Z V_g V_f).hom := by
    rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
    simp only [conjugateEquiv_symm_comp]
    congr 1
    ext N
    simpa using h N
  simpa using NatTrans.congr_app key M

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

variable {C_X C_Y C_Z D_X D_Y D_Z : Type*} [Category* C_X] [Category* C_Y] [Category* C_Z]
  [Category* D_X] [Category* D_Y] [Category* D_Z]
  {L_X : C_X ⥤ D_X} {L_Y : C_Y ⥤ D_Y} {L_Z : C_Z ⥤ D_Z}
  {G_f : C_Y ⥤ C_X} {F_f : C_X ⥤ C_Y} (adj_f : G_f ⊣ F_f)
  {G_g : C_Z ⥤ C_Y} {F_g : C_Y ⥤ C_Z} (adj_g : G_g ⊣ F_g)
  {G_fg : C_Z ⥤ C_X} {F_fg : C_X ⥤ C_Z} (adj_fg : G_fg ⊣ F_fg)
  {G'_f : D_Y ⥤ D_X} {F'_f : D_X ⥤ D_Y} (adj'_f : G'_f ⊣ F'_f)
  {G'_g : D_Z ⥤ D_Y} {F'_g : D_Y ⥤ D_Z} (adj'_g : G'_g ⊣ F'_g)
  {G'_fg : D_Z ⥤ D_X} {F'_fg : D_X ⥤ D_Z} (adj'_fg : G'_fg ⊣ F'_fg)
  (α_f : L_Y ⋙ G'_f ⟶ G_f ⋙ L_X) (β_f : F_f ⋙ L_Y ⟶ L_X ⋙ F'_f)
  (α_g : L_Z ⋙ G'_g ⟶ G_g ⋙ L_Y) (β_g : F_g ⋙ L_Z ⟶ L_Y ⋙ F'_g)
  (α_fg : L_Z ⋙ G'_fg ⟶ G_fg ⋙ L_X) (β_fg : F_fg ⋙ L_Z ⟶ L_X ⋙ F'_fg)

/-- Let `G' ⊣ F'` be adjunctions "derived" from adjunctions `G ⊣ F`, in the sense that their
units and counits are compatible with the comparisons `α : L ⋙ G' ⟶ G ⋙ L` and
`β : F ⋙ L ⟶ L ⋙ F'` (as for `Adjunction.derived`). If an isomorphism
`c' : G'_fg ≅ G'_g ⋙ G'_f` is compatible with `c : G_fg ≅ G_g ⋙ G_f` through the `α`, then its
conjugate `F'_f ⋙ F'_g ≅ F'_fg` is compatible with the conjugate of `c` through the `β`. -/
lemma conjugateEquiv_comp_app_fac (c : G_fg ≅ G_g ⋙ G_f) (c' : G'_fg ≅ G'_g ⋙ G'_f)
    (hc : ∀ M : C_Z, c'.hom.app (L_Z.obj M) ≫ G'_f.map (α_g.app M) ≫ α_f.app (G_g.obj M) =
      α_fg.app M ≫ L_X.map (c.hom.app M))
    (hη : ∀ M : C_Z, adj'_fg.unit.app (L_Z.obj M) ≫ F'_fg.map (α_fg.app M) =
      L_Z.map (adj_fg.unit.app M) ≫ β_fg.app (G_fg.obj M))
    (hε_f : ∀ N : C_X, G'_f.map (β_f.app N) ≫ adj'_f.counit.app (L_X.obj N) =
      α_f.app (F_f.obj N) ≫ L_X.map (adj_f.counit.app N))
    (hε_g : ∀ N : C_Y, G'_g.map (β_g.app N) ≫ adj'_g.counit.app (L_Y.obj N) =
      α_g.app (F_g.obj N) ≫ L_Y.map (adj_g.counit.app N))
    (K : C_X) :
    β_g.app (F_f.obj K) ≫ F'_g.map (β_f.app K) ≫
        (conjugateEquiv (adj'_g.comp adj'_f) adj'_fg c'.hom).app (L_X.obj K) =
      L_Z.map ((conjugateEquiv (adj_g.comp adj_f) adj_fg c.hom).app K) ≫ β_fg.app K := by
  have e₁ := adj'_fg.unit.naturality (β_g.app (F_f.obj K) ≫ F'_g.map (β_f.app K))
  have e₂ := c'.hom.naturality (β_g.app (F_f.obj K) ≫ F'_g.map (β_f.app K))
  have e₃ := adj'_g.counit.naturality (β_f.app K)
  have e₆ := α_f.naturality (adj_g.counit.app (F_f.obj K))
  have e₉ := β_fg.naturality (c.hom.app _ ≫ G_f.map (adj_g.counit.app _) ≫ adj_f.counit.app K)
  dsimp at e₁ e₂ e₃ e₆ e₉
  have inner : G'_fg.map (β_g.app (F_f.obj K) ≫ F'_g.map (β_f.app K)) ≫
      c'.hom.app (F'_g.obj (F'_f.obj (L_X.obj K))) ≫
        G'_f.map (adj'_g.counit.app (F'_f.obj (L_X.obj K))) ≫
        adj'_f.counit.app (L_X.obj K) =
      α_fg.app (F_g.obj (F_f.obj K)) ≫ L_X.map (c.hom.app (F_g.obj (F_f.obj K)) ≫
        G_f.map (adj_g.counit.app (F_f.obj K)) ≫
        adj_f.counit.app K) := by
    rw [reassoc_of% e₂, ← G'_f.map_comp_assoc, G'_g.map_comp, Category.assoc, e₃,
      reassoc_of% (hε_g (F_f.obj K)), G'_f.map_comp_assoc, G'_f.map_comp_assoc, hε_f,
      reassoc_of% e₆, reassoc_of% hc, L_X.map_comp, L_X.map_comp]
  dsimp only [Functor.comp_obj] at inner e₉
  simp only [conjugateEquiv_apply_app, comp_counit_app, Functor.comp_obj]
  rw [← Category.assoc, ← Category.assoc, e₁]
  have inner' := congrArg F'_fg.map inner
  simp only [Functor.map_comp, Category.assoc] at inner' e₉ ⊢
  rw [inner', reassoc_of% hη, ← e₉]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The coherence of `derivedComapLowerStarIso` with the composition isomorphisms
`Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`. -/
def DerivedComapLowerStarIsoCompCoherence : Prop :=
  ∀ N, D(Mod.comap (coefficientMap a Z)).map ((rightDerivedLowerStarComp Λ' f g).hom.app N) ≫
      (derivedComapLowerStarIso a (f ≫ g)).hom.app N =
    (derivedComapLowerStarIso a g).hom.app (R((f)_*⟦Λ'⟧).obj N) ≫
      R((g)_*⟦Λ⟧).map ((derivedComapLowerStarIso a f).hom.app N) ≫
        (rightDerivedLowerStarComp Λ f g).hom.app (D(Mod.comap (coefficientMap a X)).obj N)

/-- The derived (Pull) isomorphisms are compatible with the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, provided `derivedComapLowerStarIso` is compatible with the
composition isomorphisms `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`. -/
lemma derivedPullIso_hom_app_comp_of_derivedComapLowerStarIso
    (h : DerivedComapLowerStarIsoCompCoherence a f g) (M) :
    (derivedPullIso a (f ≫ g)).hom.app M ≫
        (leftDerivedUpperStarComp Λ' f g).hom.app
          (L(Mod.extendScalars (coefficientMap a Z)).obj M) =
      L(Mod.extendScalars (coefficientMap a X)).map
          ((leftDerivedUpperStarComp Λ f g).hom.app M) ≫
        (derivedPullIso a f).hom.app (L((g)^*⟦Λ⟧).obj M) ≫
          L((f)^*⟦Λ'⟧).map ((derivedPullIso a g).hom.app M) :=
  Adjunction.pullIsoOfComapIso_hom_app_comp (h := h) (M := M) ..

end AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory.Adjunction

variable {C'_X C'_Y C'_Z C_X C_Y C_Z D'_X D'_Y D'_Z D_X D_Y D_Z : Type*}
  [Category* C'_X] [Category* C'_Y] [Category* C'_Z] [Category* C_X] [Category* C_Y]
  [Category* C_Z] [Category* D'_X] [Category* D'_Y] [Category* D'_Z] [Category* D_X]
  [Category* D_Y] [Category* D_Z]
  {Q'_X : C'_X ⥤ D'_X} {Q'_Y : C'_Y ⥤ D'_Y} {Q'_Z : C'_Z ⥤ D'_Z}
  {Q_X : C_X ⥤ D_X} {Q_Y : C_Y ⥤ D_Y} {Q_Z : C_Z ⥤ D_Z}
  {P'_f : C'_X ⥤ C'_Y} {P'_g : C'_Y ⥤ C'_Z} {P'_fg : C'_X ⥤ C'_Z}
  {P_f : C_X ⥤ C_Y} {P_g : C_Y ⥤ C_Z} {P_fg : C_X ⥤ C_Z}
  {R'_f : D'_X ⥤ D'_Y} {R'_g : D'_Y ⥤ D'_Z} {R'_fg : D'_X ⥤ D'_Z}
  {R_f : D_X ⥤ D_Y} {R_g : D_Y ⥤ D_Z} {R_fg : D_X ⥤ D_Z}
  {H_X : C'_X ⥤ C_X} {H_Y : C'_Y ⥤ C_Y} {H_Z : C'_Z ⥤ C_Z}
  {T_X : D'_X ⥤ D_X} {T_Y : D'_Y ⥤ D_Y} {T_Z : D'_Z ⥤ D_Z}

/-- A diagram chase: let `R'`, `R` be functors between "derived" categories, with comparisons
`β : P ⋙ Q ⟶ Q ⋙ R` from functors `P` between "homotopy" categories, and let `T`, `H` be
functors compatible with the localizations `Q` through isomorphisms `φ`. Let `E_f`, `E_g`,
`E_fg : R' ⋙ T ≅ T ⋙ R` be isomorphisms induced by maps `e : P' ⋙ H ⟶ H ⋙ P` through the `β`,
and `d'`, `d` composition isomorphisms induced by `d'_h`, `d_h`. If the `e` are compatible with
`d'_h` and `d_h`, then the `E` are compatible with `d'` and `d` on the objects `Q' K` for which
the composite `β'_g ≫ R'_g β'_f` is an isomorphism. -/
lemma comp_coherence_app_Q_of_isIso
    (β'_f : P'_f ⋙ Q'_Y ⟶ Q'_X ⋙ R'_f) (β'_g : P'_g ⋙ Q'_Z ⟶ Q'_Y ⋙ R'_g)
    (β'_fg : P'_fg ⋙ Q'_Z ⟶ Q'_X ⋙ R'_fg)
    (β_f : P_f ⋙ Q_Y ⟶ Q_X ⋙ R_f) (β_g : P_g ⋙ Q_Z ⟶ Q_Y ⋙ R_g)
    (β_fg : P_fg ⋙ Q_Z ⟶ Q_X ⋙ R_fg)
    (φ_X : Q'_X ⋙ T_X ≅ H_X ⋙ Q_X) (φ_Y : Q'_Y ⋙ T_Y ≅ H_Y ⋙ Q_Y)
    (φ_Z : Q'_Z ⋙ T_Z ≅ H_Z ⋙ Q_Z)
    (E_f : R'_f ⋙ T_Y ≅ T_X ⋙ R_f) (E_g : R'_g ⋙ T_Z ≅ T_Y ⋙ R_g)
    (E_fg : R'_fg ⋙ T_Z ≅ T_X ⋙ R_fg)
    (e_f : ∀ K, H_Y.obj (P'_f.obj K) ⟶ P_f.obj (H_X.obj K))
    (e_g : ∀ K, H_Z.obj (P'_g.obj K) ⟶ P_g.obj (H_Y.obj K))
    (e_fg : ∀ K, H_Z.obj (P'_fg.obj K) ⟶ P_fg.obj (H_X.obj K))
    (d' : R'_f ⋙ R'_g ⟶ R'_fg) (d : R_f ⋙ R_g ⟶ R_fg)
    (d'_h : ∀ K, P'_g.obj (P'_f.obj K) ⟶ P'_fg.obj K)
    (d_h : ∀ K, P_g.obj (P_f.obj K) ⟶ P_fg.obj K)
    (hE_f : ∀ K, T_Y.map (β'_f.app K) ≫ E_f.hom.app (Q'_X.obj K) =
      φ_Y.hom.app (P'_f.obj K) ≫ Q_Y.map (e_f K) ≫ β_f.app (H_X.obj K) ≫
        R_f.map (φ_X.inv.app K))
    (hE_g : ∀ K, T_Z.map (β'_g.app K) ≫ E_g.hom.app (Q'_Y.obj K) =
      φ_Z.hom.app (P'_g.obj K) ≫ Q_Z.map (e_g K) ≫ β_g.app (H_Y.obj K) ≫
        R_g.map (φ_Y.inv.app K))
    (hE_fg : ∀ K, T_Z.map (β'_fg.app K) ≫ E_fg.hom.app (Q'_X.obj K) =
      φ_Z.hom.app (P'_fg.obj K) ≫ Q_Z.map (e_fg K) ≫ β_fg.app (H_X.obj K) ≫
        R_fg.map (φ_X.inv.app K))
    (hd' : ∀ K, β'_g.app (P'_f.obj K) ≫ R'_g.map (β'_f.app K) ≫ d'.app (Q'_X.obj K) =
      Q'_Z.map (d'_h K) ≫ β'_fg.app K)
    (hd : ∀ K, β_g.app (P_f.obj K) ≫ R_g.map (β_f.app K) ≫ d.app (Q_X.obj K) =
      Q_Z.map (d_h K) ≫ β_fg.app K)
    (hH : ∀ K, H_Z.map (d'_h K) ≫ e_fg K =
      e_g (P'_f.obj K) ≫ P_g.map (e_f K) ≫ d_h (H_X.obj K))
    (K : C'_X) [IsIso (β'_g.app (P'_f.obj K) ≫ R'_g.map (β'_f.app K))] :
    T_Z.map (d'.app (Q'_X.obj K)) ≫ E_fg.hom.app (Q'_X.obj K) =
      E_g.hom.app (R'_f.obj (Q'_X.obj K)) ≫ R_g.map (E_f.hom.app (Q'_X.obj K)) ≫
        d.app (T_X.obj (Q'_X.obj K)) := by
  rw [← cancel_epi (T_Z.map (β'_g.app (P'_f.obj K) ≫ R'_g.map (β'_f.app K)))]
  have h₁ := φ_Z.hom.naturality (d'_h K)
  have h₂ := E_g.hom.naturality (β'_f.app K)
  have h₃ := d.naturality (φ_X.inv.app K)
  have h₄ := β_g.naturality (e_f K)
  dsimp at h₁ h₂ h₃ h₄
  have hL : T_Z.map (β'_g.app (P'_f.obj K) ≫ R'_g.map (β'_f.app K)) ≫
      T_Z.map (d'.app (Q'_X.obj K)) ≫ E_fg.hom.app (Q'_X.obj K) =
      φ_Z.hom.app (P'_g.obj (P'_f.obj K)) ≫ Q_Z.map (H_Z.map (d'_h K) ≫ e_fg K) ≫
        β_fg.app (H_X.obj K) ≫ R_fg.map (φ_X.inv.app K) := by
    rw [← T_Z.map_comp_assoc, Category.assoc, hd', T_Z.map_comp_assoc, hE_fg,
      reassoc_of% h₁, Q_Z.map_comp_assoc]
  have hR : T_Z.map (β'_g.app (P'_f.obj K) ≫ R'_g.map (β'_f.app K)) ≫
      E_g.hom.app (R'_f.obj (Q'_X.obj K)) ≫ R_g.map (E_f.hom.app (Q'_X.obj K)) ≫
        d.app (T_X.obj (Q'_X.obj K)) =
      φ_Z.hom.app (P'_g.obj (P'_f.obj K)) ≫
        Q_Z.map (e_g (P'_f.obj K) ≫ P_g.map (e_f K) ≫ d_h (H_X.obj K)) ≫
        β_fg.app (H_X.obj K) ≫ R_fg.map (φ_X.inv.app K) := by
    rw [T_Z.map_comp_assoc, reassoc_of% h₂, reassoc_of% (hE_g (P'_f.obj K)),
      ← R_g.map_comp_assoc, ← R_g.map_comp_assoc, Category.assoc, hE_f,
      Iso.inv_hom_id_app_assoc, R_g.map_comp_assoc, R_g.map_comp_assoc, h₃,
      ← reassoc_of% h₄, reassoc_of% (hd (H_X.obj K)), Q_Z.map_comp_assoc, Q_Z.map_comp_assoc]
  rw [hL, hR, hH]

/-- The diagram chase `Adjunction.comp_coherence_app_Q_of_isIso`, on every object, provided every
object is isomorphic to some `Q' K` for which `β'_g ≫ R'_g β'_f` is an isomorphism. -/
lemma comp_coherence_app_of_isIso
    (β'_f : P'_f ⋙ Q'_Y ⟶ Q'_X ⋙ R'_f) (β'_g : P'_g ⋙ Q'_Z ⟶ Q'_Y ⋙ R'_g)
    (β'_fg : P'_fg ⋙ Q'_Z ⟶ Q'_X ⋙ R'_fg)
    (β_f : P_f ⋙ Q_Y ⟶ Q_X ⋙ R_f) (β_g : P_g ⋙ Q_Z ⟶ Q_Y ⋙ R_g)
    (β_fg : P_fg ⋙ Q_Z ⟶ Q_X ⋙ R_fg)
    (φ_X : Q'_X ⋙ T_X ≅ H_X ⋙ Q_X) (φ_Y : Q'_Y ⋙ T_Y ≅ H_Y ⋙ Q_Y)
    (φ_Z : Q'_Z ⋙ T_Z ≅ H_Z ⋙ Q_Z)
    (E_f : R'_f ⋙ T_Y ≅ T_X ⋙ R_f) (E_g : R'_g ⋙ T_Z ≅ T_Y ⋙ R_g)
    (E_fg : R'_fg ⋙ T_Z ≅ T_X ⋙ R_fg)
    (e_f : ∀ K, H_Y.obj (P'_f.obj K) ⟶ P_f.obj (H_X.obj K))
    (e_g : ∀ K, H_Z.obj (P'_g.obj K) ⟶ P_g.obj (H_Y.obj K))
    (e_fg : ∀ K, H_Z.obj (P'_fg.obj K) ⟶ P_fg.obj (H_X.obj K))
    (d' : R'_f ⋙ R'_g ⟶ R'_fg) (d : R_f ⋙ R_g ⟶ R_fg)
    (d'_h : ∀ K, P'_g.obj (P'_f.obj K) ⟶ P'_fg.obj K)
    (d_h : ∀ K, P_g.obj (P_f.obj K) ⟶ P_fg.obj K)
    (hE_f : ∀ K, T_Y.map (β'_f.app K) ≫ E_f.hom.app (Q'_X.obj K) =
      φ_Y.hom.app (P'_f.obj K) ≫ Q_Y.map (e_f K) ≫ β_f.app (H_X.obj K) ≫
        R_f.map (φ_X.inv.app K))
    (hE_g : ∀ K, T_Z.map (β'_g.app K) ≫ E_g.hom.app (Q'_Y.obj K) =
      φ_Z.hom.app (P'_g.obj K) ≫ Q_Z.map (e_g K) ≫ β_g.app (H_Y.obj K) ≫
        R_g.map (φ_Y.inv.app K))
    (hE_fg : ∀ K, T_Z.map (β'_fg.app K) ≫ E_fg.hom.app (Q'_X.obj K) =
      φ_Z.hom.app (P'_fg.obj K) ≫ Q_Z.map (e_fg K) ≫ β_fg.app (H_X.obj K) ≫
        R_fg.map (φ_X.inv.app K))
    (hd' : ∀ K, β'_g.app (P'_f.obj K) ≫ R'_g.map (β'_f.app K) ≫ d'.app (Q'_X.obj K) =
      Q'_Z.map (d'_h K) ≫ β'_fg.app K)
    (hd : ∀ K, β_g.app (P_f.obj K) ≫ R_g.map (β_f.app K) ≫ d.app (Q_X.obj K) =
      Q_Z.map (d_h K) ≫ β_fg.app K)
    (hH : ∀ K, H_Z.map (d'_h K) ≫ e_fg K =
      e_g (P'_f.obj K) ≫ P_g.map (e_f K) ≫ d_h (H_X.obj K))
    (hK : ∀ N : D'_X, ∃ K : C'_X, Nonempty (N ≅ Q'_X.obj K) ∧
      IsIso (β'_g.app (P'_f.obj K) ≫ R'_g.map (β'_f.app K)))
    (N : D'_X) :
    T_Z.map (d'.app N) ≫ E_fg.hom.app N =
      E_g.hom.app (R'_f.obj N) ≫ R_g.map (E_f.hom.app N) ≫ d.app (T_X.obj N) := by
  obtain ⟨K, ⟨i⟩, _⟩ := hK N
  have key := comp_coherence_app_Q_of_isIso β'_f β'_g β'_fg β_f β_g β_fg φ_X φ_Y φ_Z E_f E_g
    E_fg e_f e_g e_fg d' d d'_h d_h hE_f hE_g hE_fg hd' hd hH K
  have n₁ := (Functor.whiskerRight d' T_Z ≫ E_fg.hom).naturality i.inv
  have n₂ := (Functor.whiskerLeft R'_f E_g.hom ≫ Functor.whiskerRight E_f.hom R_g ≫
    Functor.whiskerLeft T_X d).naturality i.inv
  simp only [Functor.comp_obj, Functor.comp_map, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] at n₁ n₂
  rw [← cancel_epi (T_Z.map (R'_g.map (R'_f.map i.inv))), n₁, reassoc_of% key, ← n₂]

end CategoryTheory.Adjunction
