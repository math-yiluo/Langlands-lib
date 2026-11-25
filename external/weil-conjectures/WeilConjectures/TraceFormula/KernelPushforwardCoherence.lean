/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleSquareCoherence
public import WeilConjectures.TraceFormula.ProperCompatibilityExchange

/-!

# Coherence lemmas for the kernel pushforward

For a proper morphism `f : X ⟶ Y`, `q = f × f` and `K' = Rf_* K`, the kernel pushforward
`ρ_f : Rq_* (K ⊠ D_X K) ⟶ K' ⊠ D_Y K'` exchanges the evaluation kernels:
`e_{K'} ∘ ρ_f = RΔ_{Y*} τ_f ∘ Rq_* e_K` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, (1)). This file collects the ingredients of the
proof, which passes to the `LΔ_Y^* ⊣ RΔ_{Y*}` and `Lf^* ⊣ Rf_*` adjoints, where it reduces to the
coherence of the composition isomorphisms of the derived pullbacks with each other and with the
tensor comparisons (`ProEtale.CondensedRing.upperStarComp_inv_app_comp_prodUpperStarCounit`,
`ProEtale.CondensedRing.boundedConstructibleUpperStarComp_square_coherence_tensor`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- Monoidal bookkeeping: `δ ≫ ((a ≫ c₁) ⊗ (b ≫ c₂')) = δ ≫ (c₁ ⊗ c₂) ≫ (M ◁ χ)` for `a = 𝟙` and
`b ≫ c₂' = c₂ ≫ χ`. -/
private lemma comp_tensorHom_eq_of_eq {C : Type*} [Category C] [MonoidalCategory C]
    {T P Q Q' M N N' : C}
    (δ : T ⟶ P ⊗ Q) (a : P ⟶ P) (ha : a = 𝟙 P) (c₁ : P ⟶ M) (b : Q ⟶ Q') (c₂' : Q' ⟶ N')
    (c₂ : Q ⟶ N) (χ : N ⟶ N') (h : b ≫ c₂' = c₂ ≫ χ) :
    δ ≫ ((a ≫ c₁) ⊗ₘ (b ≫ c₂')) = δ ≫ (c₁ ⊗ₘ c₂) ≫ (M ◁ χ) := by
  subst ha
  rw [MonoidalCategory.tensorHom_comp_whiskerLeft, h, Category.id_comp]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Evaluation

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {A B X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The adjoint for `Lp^* ⊣ Rp_*` followed by the cast along `p = p'`. -/
@[reassoc]
lemma homEquiv_comp_eqToHom_of_eq {p p' : A ⟶ B} (h : p = p')
    {M : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {N : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : (boundedConstructibleUpperStar _ ℓ p).obj M ⟶ N) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).homEquiv _ _ φ ≫
        eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerStar ℓ r).obj N) h) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ p').homEquiv _ _
        (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj M) h.symm) ≫ φ) := by
  subst h
  simp

/-- The adjoint for `L(f ≫ g)^* ⊣ R(f ≫ g)_*` through the composition isomorphisms. -/
@[reassoc]
lemma homEquiv_comp_lowerStarComp_hom_app {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (a : X ⟶ Y) (b : Y ⟶ Z)
    {M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : (boundedConstructibleUpperStar _ ℓ a).obj ((boundedConstructibleUpperStar _ ℓ b).obj M) ⟶
      N) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ b).homEquiv _ _
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ a).homEquiv _ _ φ) ≫
      (boundedConstructibleLowerStarComp ℓ a b).hom.app N =
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (a ≫ b)).homEquiv _ _
      ((boundedConstructibleUpperStarComp _ ℓ a b).hom.app M ≫ φ) :=
  Adjunction.homEquiv_homEquiv_comp_hom_app _ _ _ _ _ rfl φ

/-- The adjoint for `L(f ≫ g)^* ⊣ R(f ≫ g)_*` followed by the inverse composition isomorphism. -/
@[reassoc]
lemma homEquiv_comp_lowerStarComp_inv_app {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] (a : X ⟶ Y) (b : Y ⟶ Z)
    {M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : (boundedConstructibleUpperStar _ ℓ (a ≫ b)).obj M ⟶ N) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (a ≫ b)).homEquiv _ _ φ ≫
      (boundedConstructibleLowerStarComp ℓ a b).inv.app N =
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ b).homEquiv _ _
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ a).homEquiv _ _
        ((boundedConstructibleUpperStarComp _ ℓ a b).inv.app M ≫ φ)) := by
  rw [← cancel_mono ((boundedConstructibleLowerStarComp ℓ a b).hom.app N), Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, homEquiv_comp_lowerStarComp_hom_app,
    Iso.hom_inv_id_app_assoc]

-- the pullbacks of bounded constructible complexes are unfolded in the defeq checks
/-- The identification `LΔ^* (K ⊠ N) ≅ K ⊗ N` is natural in `N`. -/
@[reassoc]
lemma diagUpperStarExternalProductIso_hom_naturality_right
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {N N' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (χ : N ⟶ N') :
    (boundedConstructibleUpperStar _ ℓ (diag X)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj M ◁
          (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map χ) ≫
      (diagUpperStarExternalProductIso ℓ M N').hom =
    (diagUpperStarExternalProductIso ℓ M N).hom ≫ (M ◁ χ) := by
  have h₂ : diag X ≫ (prod.snd : X ⨯ X ⟶ X) = 𝟙 X := by simp [diag]
  have n₁ :=
    (boundedConstructibleUpperStarComp _ ℓ (diag X) (prod.snd : X ⨯ X ⟶ X)).inv.naturality χ
  have n₂ := boundedConstructibleUpperStar_map_eqToHom_id _ ℓ h₂ χ
  simp only [Functor.comp_map] at n₁
  unfold externalProduct at *
  simp only [diagUpperStarExternalProductIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.app_inv, Iso.app_hom, eqToIso.hom, Category.assoc, Functor.Monoidal.μIso_inv]
  have d := δ_natural (boundedConstructibleUpperStar _ ℓ (diag X))
    (𝟙 ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).obj M))
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map χ)
  rw [← MonoidalCategory.id_tensorHom, ← reassoc_of% d, MonoidalCategory.tensorHom_comp_tensorHom]
  have h : (boundedConstructibleUpperStar _ ℓ (diag X)).map
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).map χ) ≫
      (boundedConstructibleUpperStarComp _ ℓ (diag X) (prod.snd : X ⨯ X ⟶ X)).inv.app N' ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar _ ℓ u).obj N') h₂) ≫
      (boundedConstructibleUpperStarId _ ℓ X).hom.app N' =
    ((boundedConstructibleUpperStarComp _ ℓ (diag X) (prod.snd : X ⨯ X ⟶ X)).inv.app N ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar _ ℓ u).obj N) h₂) ≫
      (boundedConstructibleUpperStarId _ ℓ X).hom.app N) ≫ χ := by
    simp only [Category.assoc]
    rw [reassoc_of% n₁, n₂]
  exact comp_tensorHom_eq_of_eq _ _ (CategoryTheory.Functor.map_id _ _) _ _ _ _ _ h


-- the pullbacks of bounded constructible complexes are unfolded in the defeq checks
/-- The `Lf^*`-side of the exchange of the evaluation kernels: the adjoint of the Künneth map
`Π : Rf_* K ⊠ Rf_* N ⟶ Rq_* (K ⊠ N)` (`q = f × f`), read through the composition isomorphisms
along `ΔX ≫ q = f ≫ ΔY` and the identifications `LΔ^* (M ⊠ M') ≅ M ⊗ M'`, is
`Lf^* LΔ_Y^* (Rf_* K ⊠ Rf_* N) ≅ Lf^* (Rf_* K ⊗ Rf_* N) ⟶ Lf^* Rf_* K ⊗ Lf^* Rf_* N ⟶ K ⊗ N`. -/
@[reassoc]
lemma upperStarComp_inv_app_comp_prodUpperStarCounit (f : X ⟶ Y)
    (K N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (hΔ : diag X ≫ prod.map f f = f ≫ diag Y) :
    (boundedConstructibleUpperStarComp _ ℓ f (diag Y)).inv.app
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
        ((boundedConstructibleLowerStar ℓ f).obj N)) ≫
    eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
        ((boundedConstructibleLowerStar ℓ f).obj N))) hΔ.symm) ≫
    (boundedConstructibleUpperStarComp _ ℓ (diag X) (prod.map f f)).hom.app
      (externalProduct ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
        ((boundedConstructibleLowerStar ℓ f).obj N)) ≫
    (boundedConstructibleUpperStar _ ℓ (diag X)).map
      ((Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (prod.map f f)) _ _).inv ≫
        (prodUpperStarCounit ℓ (prod.map_fst f f) K ⊗ₘ
          prodUpperStarCounit ℓ (prod.map_snd f f) N)) ≫
    (diagUpperStarExternalProductIso ℓ K N).hom =
  (boundedConstructibleUpperStar _ ℓ f).map
      (diagUpperStarExternalProductIso ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
        ((boundedConstructibleLowerStar ℓ f).obj N)).hom ≫
    Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ f) _ _ ≫
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app K ⊗ₘ
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit.app
        N) := by
  simp only [diagUpperStarExternalProductIso, prodUpperStarCounit, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Iso.app_inv, Iso.app_hom, eqToIso.hom, Functor.Monoidal.μIso_inv,
    Functor.map_comp, Category.assoc]
  exact boundedConstructibleUpperStarComp_square_coherence_tensor ℓ f (diag X) (diag Y)
    (prod.map f f) prod.fst prod.snd prod.fst prod.snd hΔ.symm (prod.map_fst f f)
    (prod.map_snd f f) (by simp [diag]) (by simp [diag]) (by simp [diag]) (by simp [diag]) _ _

end Evaluation

end AlgebraicGeometry.ProEtale.CondensedRing
