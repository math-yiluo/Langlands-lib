/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp

/-!
# Coherence of the composition isomorphisms of derived pullbacks in a square

For a commutative square `ΔX ≫ q = f ≫ ΔY` of `k`-schemes with projections `pᵢ`, `p'ᵢ`
satisfying `q ≫ pᵢ = p'ᵢ ≫ f`, `ΔY ≫ pᵢ = 𝟙` and `ΔX ≫ p'ᵢ = 𝟙` (the diagonal squares of a
morphism `f` and of `f × f`), the two identifications `Lf^* LΔ_Y^* Lp^* A ≅ Lf^* A` built from
the composition isomorphisms of the derived pullbacks of bounded constructible complexes agree
(`ProEtale.CondensedRing.boundedConstructibleUpperStarComp_square_coherence`), also after tensoring
through the monoidal structures
(`ProEtale.CondensedRing.boundedConstructibleUpperStarComp_square_coherence_tensor`). These are
consequences of the associativity and unit laws of the composition isomorphisms and of their
monoidality.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Coherence

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {W X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsSeparated W.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- Associativity of the composition isomorphisms, with the inner one inverted. -/
lemma boundedConstructibleUpperStarComp_hom_app_map_inv_app (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) (A : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ a b).hom.app
        ((boundedConstructibleUpperStar Λ ℓ c).obj A) ≫
      (boundedConstructibleUpperStar Λ ℓ a).map
        ((boundedConstructibleUpperStarComp Λ ℓ b c).inv.app A) =
    (boundedConstructibleUpperStarComp Λ ℓ (a ≫ b) c).inv.app A ≫
      eqToHom (by rw [Category.assoc]) ≫
      (boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).hom.app A := by
  rw [← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ (a ≫ b) c).hom.app A),
    reassoc_of% (boundedConstructibleUpperStarComp_assoc_app Λ ℓ a b c A)]
  simp [← Functor.map_comp]

/-- Associativity of the composition isomorphisms, with the outer one inverted. -/
lemma boundedConstructibleUpperStar_map_hom_app_comp_inv_app (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) (A : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStar Λ ℓ a).map
        ((boundedConstructibleUpperStarComp Λ ℓ b c).hom.app A) ≫
      (boundedConstructibleUpperStarComp Λ ℓ a b).inv.app
        ((boundedConstructibleUpperStar Λ ℓ c).obj A) =
    (boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).inv.app A ≫
      eqToHom (by rw [Category.assoc]) ≫
      (boundedConstructibleUpperStarComp Λ ℓ (a ≫ b) c).hom.app A := by
  have h := boundedConstructibleUpperStarComp_assoc_app Λ ℓ a b c A
  rw [← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).hom.app A),
    ← cancel_epi (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj A)
      (Category.assoc a b c)))]
  rw [← reassoc_of% h]
  simp

/-- Associativity of the composition isomorphisms, both inverted. -/
lemma boundedConstructibleUpperStarComp_inv_app_comp_inv_app' (a : W ⟶ X) (b : X ⟶ Y)
    (c : Y ⟶ Z) (A : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ a b).inv.app
        ((boundedConstructibleUpperStar Λ ℓ c).obj A) ≫
      (boundedConstructibleUpperStarComp Λ ℓ (a ≫ b) c).inv.app A =
    (boundedConstructibleUpperStar Λ ℓ a).map
        ((boundedConstructibleUpperStarComp Λ ℓ b c).inv.app A) ≫
      (boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).inv.app A ≫
      eqToHom (by rw [Category.assoc]) := by
  have h := boundedConstructibleUpperStarComp_assoc_app Λ ℓ a b c A
  rw [← cancel_epi ((boundedConstructibleUpperStar Λ ℓ a).map
      ((boundedConstructibleUpperStarComp Λ ℓ b c).hom.app A)),
    ← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ a (b ≫ c)).hom.app A),
    ← cancel_epi (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj A)
      (Category.assoc a b c)))]
  rw [← reassoc_of% h]
  simp [← Functor.map_comp_assoc]

/-- The composition isomorphisms with a common first map are compatible with the casts along
`r = r'`. -/
lemma boundedConstructibleUpperStarComp_hom_app_map_eqToHom_inv_app {r r' : X ⟶ Z} (h : r = r')
    (a : W ⟶ X) (A : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ a r).hom.app A ≫
      (boundedConstructibleUpperStar Λ ℓ a).map
        (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj A) h)) ≫
      (boundedConstructibleUpperStarComp Λ ℓ a r').inv.app A =
    eqToHom (by rw [h]) := by
  subst h
  simp

/-- The composition isomorphisms with a common second map are compatible with the casts along
`u = u'`. -/
lemma eqToHom_comp_boundedConstructibleUpperStarComp_inv_app {u u' : W ⟶ X} (h : u = u')
    (v : X ⟶ Z) (A : Dᵇc(Z.left)⟦Λ⟧) :
    eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ v).obj A)) h) ≫
      (boundedConstructibleUpperStarComp Λ ℓ u' v).inv.app A =
    (boundedConstructibleUpperStarComp Λ ℓ u v).inv.app A ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The left unit law of the composition isomorphisms, for a map `r` equal to the identity. -/
lemma boundedConstructibleUpperStarComp_hom_app_eqToHom_id {r : X ⟶ X} (h : r = 𝟙 X)
    (f : X ⟶ Y) (A : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ r f).hom.app A ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ f).obj A)) h) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app
        ((boundedConstructibleUpperStar Λ ℓ f).obj A) =
    eqToHom (by rw [h, Category.id_comp]; rfl) := by
  subst h
  simpa using boundedConstructibleUpperStarComp_id_left_app Λ ℓ f A

/-- The right unit law of the composition isomorphisms, for a map `r` equal to the identity. -/
lemma boundedConstructibleUpperStarComp_inv_app_eqToHom_id {r : Y ⟶ Y} (h : r = 𝟙 Y)
    (f : X ⟶ Y) (A : Dᵇc(Y.left)⟦Λ⟧)
    (h' : (boundedConstructibleUpperStar Λ ℓ (f ≫ r)).obj A =
      (boundedConstructibleUpperStar Λ ℓ f).obj A) :
    (boundedConstructibleUpperStarComp Λ ℓ f r).inv.app A ≫ eqToHom h' =
      (boundedConstructibleUpperStar Λ ℓ f).map
        (eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h) ≫
          (boundedConstructibleUpperStarId Λ ℓ Y).hom.app A) := by
  subst h
  rw [← cancel_epi ((boundedConstructibleUpperStarComp Λ ℓ f (𝟙 Y)).hom.app A)]
  simpa using (boundedConstructibleUpperStarComp_id_right_app Λ ℓ f A).symm

/-- The two identifications `Lf^* LΔ_Y^* Lp^* A ≅ Lf^* A` in the square `ΔX ≫ q = f ≫ ΔY` with
`q ≫ p = p' ≫ f`, `ΔY ≫ p = 𝟙` and `ΔX ≫ p' = 𝟙` agree. -/
lemma boundedConstructibleUpperStarComp_square_coherence (f : X ⟶ Y) (ΔX : X ⟶ W)
    (ΔY : Y ⟶ Z) (q : W ⟶ Z) (p : Z ⟶ Y) (p' : W ⟶ X) (h₁ : f ≫ ΔY = ΔX ≫ q)
    (h₂ : q ≫ p = p' ≫ f) (h₃ : ΔY ≫ p = 𝟙 Y) (h₄ : ΔX ≫ p' = 𝟙 X) (A : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ f ΔY).inv.app
        ((boundedConstructibleUpperStar Λ ℓ p).obj A) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ p).obj A)) h₁) ≫
      (boundedConstructibleUpperStarComp Λ ℓ ΔX q).hom.app
        ((boundedConstructibleUpperStar Λ ℓ p).obj A) ≫
      (boundedConstructibleUpperStar Λ ℓ ΔX).map
        ((boundedConstructibleUpperStarComp Λ ℓ q p).inv.app A ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₂) ≫
          (boundedConstructibleUpperStarComp Λ ℓ p' f).hom.app A) ≫
      (boundedConstructibleUpperStarComp Λ ℓ ΔX p').inv.app
        ((boundedConstructibleUpperStar Λ ℓ f).obj A) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ f).obj A)) h₄) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app
        ((boundedConstructibleUpperStar Λ ℓ f).obj A) =
    (boundedConstructibleUpperStar Λ ℓ f).map
      ((boundedConstructibleUpperStarComp Λ ℓ ΔY p).inv.app A ≫
        eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₃) ≫
        (boundedConstructibleUpperStarId Λ ℓ Y).hom.app A) := by
  have e₁ := boundedConstructibleUpperStarComp_hom_app_map_inv_app Λ ℓ ΔX q p A
  have e₂ := boundedConstructibleUpperStar_map_hom_app_comp_inv_app Λ ℓ ΔX p' f A
  have e₃ := boundedConstructibleUpperStarComp_hom_app_map_eqToHom_inv_app Λ ℓ h₂ ΔX A
  have e₄ := boundedConstructibleUpperStarComp_hom_app_eqToHom_id Λ ℓ h₄ f A
  have e₅ := eqToHom_comp_boundedConstructibleUpperStarComp_inv_app Λ ℓ h₁ p A
  have e₆ := boundedConstructibleUpperStarComp_inv_app_comp_inv_app' Λ ℓ f ΔY p A
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% e₁, reassoc_of% e₂, reassoc_of% e₃, e₄, reassoc_of% e₅,
    reassoc_of% e₆]
  simp only [eqToHom_trans]
  rw [boundedConstructibleUpperStarComp_inv_app_eqToHom_id Λ ℓ h₃ f A]
  simp only [Functor.map_comp]

/-- The identification `Lr^* ≅ 𝟭` for a map `r` equal to the identity is natural. -/
lemma boundedConstructibleUpperStar_map_eqToHom_id {r : X ⟶ X} (h : r = 𝟙 X)
    {M K : Dᵇc(X.left)⟦Λ⟧} (φ : M ⟶ K) :
    (boundedConstructibleUpperStar Λ ℓ r).map φ ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj K) h) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app K =
    eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj M) h) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app M ≫ φ := by
  subst h
  simp

/-- `boundedConstructibleUpperStarComp_square_coherence` followed by a map `φ : Lf^* A ⟶ K`. -/
lemma boundedConstructibleUpperStarComp_square_coherence_comp (f : X ⟶ Y) (ΔX : X ⟶ W)
    (ΔY : Y ⟶ Z) (q : W ⟶ Z) (p : Z ⟶ Y) (p' : W ⟶ X) (h₁ : f ≫ ΔY = ΔX ≫ q)
    (h₂ : q ≫ p = p' ≫ f) (h₃ : ΔY ≫ p = 𝟙 Y) (h₄ : ΔX ≫ p' = 𝟙 X) {A : Dᵇc(Y.left)⟦Λ⟧}
    {K : Dᵇc(X.left)⟦Λ⟧} (φ : (boundedConstructibleUpperStar Λ ℓ f).obj A ⟶ K) :
    (boundedConstructibleUpperStarComp Λ ℓ f ΔY).inv.app
        ((boundedConstructibleUpperStar Λ ℓ p).obj A) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ p).obj A)) h₁) ≫
      (boundedConstructibleUpperStarComp Λ ℓ ΔX q).hom.app
        ((boundedConstructibleUpperStar Λ ℓ p).obj A) ≫
      (boundedConstructibleUpperStar Λ ℓ ΔX).map
        ((boundedConstructibleUpperStarComp Λ ℓ q p).inv.app A ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₂) ≫
          (boundedConstructibleUpperStarComp Λ ℓ p' f).hom.app A ≫
          (boundedConstructibleUpperStar Λ ℓ p').map φ) ≫
      (boundedConstructibleUpperStarComp Λ ℓ ΔX p').inv.app K ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj K) h₄) ≫
      (boundedConstructibleUpperStarId Λ ℓ X).hom.app K =
    (boundedConstructibleUpperStar Λ ℓ f).map
      ((boundedConstructibleUpperStarComp Λ ℓ ΔY p).inv.app A ≫
        eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj A) h₃) ≫
        (boundedConstructibleUpperStarId Λ ℓ Y).hom.app A) ≫ φ := by
  have n₁ := (boundedConstructibleUpperStarComp Λ ℓ ΔX p').inv.naturality φ
  have n₂ := boundedConstructibleUpperStar_map_eqToHom_id Λ ℓ h₄ φ
  have c := boundedConstructibleUpperStarComp_square_coherence Λ ℓ f ΔX ΔY q p p' h₁ h₂ h₃ h₄ A
  simp only [Functor.comp_map] at n₁
  simp only [Functor.map_comp, Category.assoc] at c ⊢
  rw [reassoc_of% n₁, n₂, reassoc_of% c]



/-- The monoidality of the composition isomorphisms, inverted. -/
lemma boundedConstructibleUpperStarComp_inv_app_tensor_δ (f : X ⟶ Y) (g : Y ⟶ Z)
    (K M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).inv.app (K ⊗ M) ≫
        δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g)) K M =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map (δ
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) K M) ≫
        δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) _ _ ≫
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).inv.app K ⊗ₘ
          (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).inv.app M) := by
  have h := boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ f g K M
  rw [← cancel_epi ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f
      g).hom.app (K ⊗ M)),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% h, MonoidalCategory.tensorHom_comp_tensorHom]
  simp

/-- The tensor comparisons of the pullbacks along `r = r'` agree up to the casts. -/
lemma eqToHom_comp_δ_boundedConstructibleUpperStar {r r' : X ⟶ Y} (h : r = r')
    (K M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        u).obj (K ⊗ M)) h) ≫
        δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r') K M =
      δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r) K M ≫
        (eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            u).obj K) h) ⊗ₘ
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
              ℓ u).obj M) h)) := by
  subst h
  simp

/-- The tensor form of `boundedConstructibleUpperStarComp_square_coherence_comp`: the two
identifications `Lf^* LΔ_Y^* (Lp₁^* A ⊗ Lp₂^* B) ⟶ K ⊗ N` in the square `ΔX ≫ q = f ≫ ΔY` with
`q ≫ pᵢ = p'ᵢ ≫ f`, `ΔY ≫ pᵢ = 𝟙` and `ΔX ≫ p'ᵢ = 𝟙`, through `φ : Lf^* A ⟶ K` and
`ψ : Lf^* B ⟶ N`, agree. -/
lemma boundedConstructibleUpperStarComp_square_coherence_tensor (f : X ⟶ Y) (ΔX : X ⟶ W)
    (ΔY : Y ⟶ Z) (q : W ⟶ Z) (p₁ p₂ : Z ⟶ Y) (p₁' p₂' : W ⟶ X) (h₁ : f ≫ ΔY = ΔX ≫ q)
    (h₂ : q ≫ p₁ = p₁' ≫ f) (h₂' : q ≫ p₂ = p₂' ≫ f) (h₃ : ΔY ≫ p₁ = 𝟙 Y)
    (h₃' : ΔY ≫ p₂ = 𝟙 Y) (h₄ : ΔX ≫ p₁' = 𝟙 X) (h₄' : ΔX ≫ p₂' = 𝟙 X)
    {A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {K N :
        Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj A ⟶ K)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj B ⟶ N) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f ΔY).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₁).obj A ⊗
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₂).obj B) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          u).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₁).obj A ⊗
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₂).obj B)) h₁) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΔX q).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₁).obj A ⊗
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₂).obj B) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΔX).map
        (δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q) _ _) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΔX).map
        (((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ q p₁).inv.app A ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
              ℓ u).obj A) h₂) ≫
          (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p₁' f).hom.app A ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₁').map φ) ⊗ₘ
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ q p₂).inv.app B ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
              ℓ u).obj B) h₂') ≫
          (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p₂' f).hom.app B ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₂').map ψ)) ≫
      δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΔX) _ _ ≫
      (((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΔX p₁').inv.app K ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
              ℓ u).obj K) h₄) ≫
          (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K) ⊗ₘ
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΔX p₂').inv.app N ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
              ℓ u).obj N) h₄') ≫
          (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app N)) =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        (δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΔY) _ _) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
        (((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΔY p₁).inv.app A ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
              ℓ u).obj A) h₃) ≫
          (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).hom.app A) ⊗ₘ
        ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΔY p₂).inv.app B ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
              ℓ u).obj B) h₃') ≫
          (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ Y).hom.app B)) ≫
      δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) _ _ ≫ (φ ⊗ₘ ψ) := by
  -- Simplifier matching avoids unfolding the pullback constructions at unrelated occurrences.
  simp only [← Functor.OplaxMonoidal.δ_natural_assoc]
  simp only [← reassoc_of% (boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ ΔX q _ _)]
  simp only [reassoc_of% (eqToHom_comp_δ_boundedConstructibleUpperStar ℓ h₁
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₁).obj A)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₂).obj B))]
  simp only [reassoc_of% (boundedConstructibleUpperStarComp_inv_app_tensor_δ ℓ f ΔY
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₁).obj A)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p₂).obj B))]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [boundedConstructibleUpperStarComp_square_coherence_comp
      (Profinite.padicAlgClRingObj ℓ) ℓ f ΔX ΔY q p₁ p₁' h₁ h₂ h₃ h₄,
    boundedConstructibleUpperStarComp_square_coherence_comp
      (Profinite.padicAlgClRingObj ℓ) ℓ f ΔX ΔY q p₂ p₂' h₁ h₂' h₃' h₄']

end Coherence

end AlgebraicGeometry.ProEtale.CondensedRing
