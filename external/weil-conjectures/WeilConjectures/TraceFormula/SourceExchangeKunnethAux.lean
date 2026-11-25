/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeCoherence

/-!

# Auxiliary lemmas for the kernel pushforward and the Künneth–Verdier isomorphisms

Abstract categorical identities used for identity (a) of the trace-class source exchange
(blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 3), and the compatibility of the
identification `Lq^* Lπ^* ≅ Lp^* Lf^*` of a commutative square with the tensor structures
(`ProEtale.CondensedRing.upperStarComp_square_tensor_δ`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

lemma _root_.CategoryTheory.MonoidalCategory.whiskerLeft_whiskerLeft_map_comp_evaluation
    {C E : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [Category E]
    [MonoidalCategory E] (U : E ⥤ C) [U.LaxMonoidal] (P : C) (N : E) {D D' W : E}
    (x : D' ⟶ D) (e : N ⊗ D ⟶ W) (g : N ⊗ D' ⟶ W) (hg : N ◁ x ≫ e = g) :
    U.obj N ◁ (P ◁ U.map x) ≫ (α_ _ _ _).inv ≫ ((β_ (U.obj N) P).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (P ◁ Functor.LaxMonoidal.μ U N D) ≫ (P ◁ U.map e) =
      (α_ _ _ _).inv ≫ ((β_ (U.obj N) P).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (P ◁ Functor.LaxMonoidal.μ U N D') ≫ (P ◁ U.map g) := by
  subst hg
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, Functor.LaxMonoidal.μ_natural_right,
    MonoidalCategory.whiskerLeft_comp_assoc]

lemma _root_.CategoryTheory.Functor.map_whiskerLeft_map_comp_eq {𝒞 𝒟 𝒠 : Type*} [Category 𝒞]
    [MonoidalCategory 𝒞] [Category 𝒟] [Category 𝒠] (L : 𝒞 ⥤ 𝒟) (U : 𝒠 ⥤ 𝒞) (P : 𝒞)
    {A A₁ A₂ A₃ Q Q' : 𝒞} {E₁ E₂ E₃ E₄ : 𝒠} {Z : 𝒟} (a₁ : A ⟶ A₁) (a₂ : A₁ ⟶ A₂)
    (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ P ⊗ U.obj E₁) (m₁ : E₁ ⟶ E₂)
    (m₂ : E₂ ⟶ E₃) (τ : E₃ ⟶ E₄) (ex : L.obj (P ⊗ U.obj E₄) ⟶ Z) (pr : P ⊗ U.obj E₃ ⟶ Q)
    (σ : Q ⟶ Q') (T : L.obj Q' ⟶ Z) (W : A ⟶ Q')
    (h₂ : L.map (P ◁ U.map τ) ≫ ex = L.map pr ≫ L.map σ ≫ T)
    (h₁ : a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ P ◁ U.map (m₁ ≫ m₂) ≫ pr ≫ σ = W) :
    L.map (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ P ◁ U.map (m₁ ≫ m₂ ≫ τ)) ≫ ex = L.map W ≫ T := by
  rw [← h₁]
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc, h₂]

lemma _root_.CategoryTheory.NatIso.map_map₆_comp_hom_app_comp_map_comp_hom_app {𝒱 𝒲 𝒳 𝒴 : Type*}
    [Category 𝒱] [Category 𝒲] [Category 𝒳] [Category 𝒴] (F₁ : 𝒲 ⥤ 𝒴) (G : 𝒱 ⥤ 𝒲) (H : 𝒱 ⥤ 𝒳)
    {Lf Sf : 𝒳 ⥤ 𝒴} (s : G ⋙ F₁ ≅ H ⋙ Lf) (σ : Lf ≅ Sf) {V₀ V₁ V₂ V₃ V₄ V₅ V₆ : 𝒱} {Z : 𝒳}
    (y₁ : V₀ ⟶ V₁) (y₂ : V₁ ⟶ V₂) (y₃ : V₂ ⟶ V₃) (y₄ : V₃ ⟶ V₄) (y₅ : V₄ ⟶ V₅)
    (y₆ : V₅ ⟶ V₆) (e : H.obj V₆ ⟶ Z) :
    F₁.map (G.map y₁) ≫ F₁.map (G.map y₂) ≫ F₁.map (G.map y₃) ≫ F₁.map (G.map y₄) ≫
        F₁.map (G.map y₅) ≫ F₁.map (G.map y₆) ≫ s.hom.app V₆ ≫ Lf.map e ≫ σ.hom.app Z =
      s.hom.app V₀ ≫ Lf.map (H.map y₁) ≫ σ.hom.app _ ≫ Sf.map (H.map y₂) ≫ Sf.map (H.map y₃) ≫
        Sf.map (H.map y₄) ≫ Sf.map (H.map y₅) ≫ Sf.map (H.map y₆) ≫ Sf.map e := by
  have h := s.hom.naturality (y₁ ≫ y₂ ≫ y₃ ≫ y₄ ≫ y₅ ≫ y₆)
  have h' := σ.hom.naturality (H.map y₂ ≫ H.map y₃ ≫ H.map y₄ ≫ H.map y₅ ≫ H.map y₆ ≫ e)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at h h'
  rw [reassoc_of% h, h']

lemma _root_.CategoryTheory.Functor.OplaxMonoidal.map_evaluation_comp_δ {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] [MonoidalCategory 𝒞] [MonoidalCategory 𝒟] [BraidedCategory 𝒞]
    [BraidedCategory 𝒟] (G : 𝒟 ⥤ 𝒞) [G.OplaxMonoidal]
    (hbraid : ∀ A B : 𝒟, G.map (β_ A B).hom ≫ Functor.OplaxMonoidal.δ G B A =
      Functor.OplaxMonoidal.δ G A B ≫ (β_ (G.obj A) (G.obj B)).hom)
    {a b d v w : 𝒟} {Ka Wb Vd Vw E : 𝒞} (x₁ : a ⊗ d ⟶ v) (x₂ : v ⟶ w) (cb : G.obj b ⟶ Wb)
    (ca : G.obj a ⟶ Ka) (cd : G.obj d ⟶ Vd) (cw : G.obj w ⟶ Vw) (m : Ka ⊗ Vd ⟶ E)
    (e : E ⟶ Vw)
    (h : G.map (x₁ ≫ x₂) ≫ cw = Functor.OplaxMonoidal.δ G a d ≫ (ca ⊗ₘ cd) ≫ m ≫ e) :
    G.map ((α_ a b d).inv ≫ (β_ a b).hom ▷ d ≫ (α_ b a d).hom ≫ b ◁ x₁ ≫ b ◁ x₂) ≫
        Functor.OplaxMonoidal.δ G b w ≫ (cb ⊗ₘ cw) =
      Functor.OplaxMonoidal.δ G a (b ⊗ d) ≫
        G.obj a ◁ (Functor.OplaxMonoidal.δ G b d ≫ (cb ⊗ₘ cd)) ≫ ca ▷ (Wb ⊗ Vd) ≫
        (α_ _ _ _).inv ≫ (β_ Ka Wb).hom ▷ Vd ≫ (α_ _ _ _).hom ≫ Wb ◁ m ≫ Wb ◁ e := by
  have h' : G.map (b ◁ x₁) ≫ G.map (b ◁ x₂) ≫ Functor.OplaxMonoidal.δ G b w ≫ (cb ⊗ₘ cw) =
      Functor.OplaxMonoidal.δ G b (a ⊗ d) ≫ (cb ⊗ₘ (Functor.OplaxMonoidal.δ G a d ≫
        (ca ⊗ₘ cd) ≫ m ≫ e)) := by
    rw [← h, ← G.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      ← Functor.OplaxMonoidal.δ_natural_right_assoc, MonoidalCategory.tensorHom_def',
      MonoidalCategory.tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc,
      Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp, Category.assoc, h']
  have h₃ := Functor.OplaxMonoidal.associativity G b a d
  have h₂ := Functor.OplaxMonoidal.δ_natural_left G (β_ a b).hom d
  have h₁ := Functor.OplaxMonoidal.associativity_inv G a b d
  have hnat : (α_ (G.obj a) (G.obj b) (G.obj d)).inv ≫ (β_ (G.obj a) (G.obj b)).hom ▷ G.obj d ≫
      (α_ (G.obj b) (G.obj a) (G.obj d)).hom ≫ (cb ⊗ₘ ((ca ⊗ₘ cd) ≫ m ≫ e)) =
      G.obj a ◁ (cb ⊗ₘ cd) ≫ ca ▷ (Wb ⊗ Vd) ≫ (α_ _ _ _).inv ≫ (β_ Ka Wb).hom ▷ Vd ≫
        (α_ _ _ _).hom ≫ Wb ◁ m ≫ Wb ◁ e := by
    have k1 : cb ⊗ₘ ((ca ⊗ₘ cd) ≫ m ≫ e) = (cb ⊗ₘ (ca ⊗ₘ cd)) ≫ Wb ◁ m ≫ Wb ◁ e := by
      rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.id_tensorHom,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    have k2 : G.obj a ◁ (cb ⊗ₘ cd) ≫ ca ▷ (Wb ⊗ Vd) = ca ⊗ₘ (cb ⊗ₘ cd) :=
      (MonoidalCategory.tensorHom_def' _ _).symm
    have k3 : ((ca ⊗ₘ cb) ⊗ₘ cd) ≫ (β_ Ka Wb).hom ▷ Vd =
        (β_ (G.obj a) (G.obj b)).hom ▷ G.obj d ≫ ((cb ⊗ₘ ca) ⊗ₘ cd) := by
      rw [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
        BraidedCategory.braiding_naturality, Category.comp_id, Category.id_comp]
    rw [k1, reassoc_of% k2, MonoidalCategory.associator_inv_naturality_assoc, reassoc_of% k3,
      MonoidalCategory.associator_naturality_assoc]
  have k4 : cb ⊗ₘ (Functor.OplaxMonoidal.δ G a d ≫ (ca ⊗ₘ cd) ≫ m ≫ e) =
      G.obj b ◁ Functor.OplaxMonoidal.δ G a d ≫ (cb ⊗ₘ ((ca ⊗ₘ cd) ≫ m ≫ e)) := by
    rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp]
  rw [k4, ← reassoc_of% h₃, ← reassoc_of% h₂, ← MonoidalCategory.comp_whiskerRight_assoc, hbraid,
    MonoidalCategory.comp_whiskerRight_assoc, ← reassoc_of% h₁, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, hnat]

lemma _root_.CategoryTheory.Adjunction.map_μ_comp_homEquiv_comp {𝒜 𝒞 𝒳 𝒴 : Type*} [Category 𝒜]
    [Category 𝒞] [Category 𝒳] [Category 𝒴] [MonoidalCategory 𝒜] [MonoidalCategory 𝒞]
    [MonoidalCategory 𝒳] [MonoidalCategory 𝒴] (Q : 𝒜 ⥤ 𝒞) [Q.OplaxMonoidal] (U₂ : 𝒴 ⥤ 𝒜)
    [U₂.Monoidal] (P₂ : 𝒳 ⥤ 𝒞) [P₂.Monoidal] (F : 𝒴 ⥤ 𝒳) [F.OplaxMonoidal] {S : 𝒳 ⥤ 𝒴}
    (adj : F ⊣ S) (Θ : ∀ M : 𝒴, Q.obj (U₂.obj M) ⟶ P₂.obj (F.obj M))
    (hnat : ∀ {M M' : 𝒴} (g : M ⟶ M'), Q.map (U₂.map g) ≫ Θ M' = Θ M ≫ P₂.map (F.map g))
    (hΘ : ∀ M₁ M₂ : 𝒴, Θ (M₁ ⊗ M₂) ≫ P₂.map (Functor.OplaxMonoidal.δ F M₁ M₂) ≫
        Functor.OplaxMonoidal.δ P₂ _ _ =
      Q.map (Functor.OplaxMonoidal.δ U₂ M₁ M₂) ≫ Functor.OplaxMonoidal.δ Q _ _ ≫
        (Θ M₁ ⊗ₘ Θ M₂))
    (c : ∀ B : 𝒳, Q.obj (U₂.obj (S.obj B)) ⟶ P₂.obj B)
    (hc : ∀ B, c B = Θ (S.obj B) ≫ P₂.map (adj.counit.app B))
    (B₁ B₂ B : 𝒳) (e : B₁ ⊗ B₂ ⟶ B) :
    Q.map (Functor.LaxMonoidal.μ U₂ (S.obj B₁) (S.obj B₂) ≫
        U₂.map (adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F (S.obj B₁) (S.obj B₂) ≫
          (adj.counit.app B₁ ⊗ₘ adj.counit.app B₂)) ≫ S.map e)) ≫
      c B =
    Functor.OplaxMonoidal.δ Q _ _ ≫ (c B₁ ⊗ₘ c B₂) ≫ Functor.LaxMonoidal.μ P₂ B₁ B₂ ≫ P₂.map e := by
  simp only [hc]
  have h₁ : Θ (S.obj B₁ ⊗ S.obj B₂) ≫ P₂.map (Functor.OplaxMonoidal.δ F _ _) =
      Q.map (Functor.OplaxMonoidal.δ U₂ _ _) ≫ Functor.OplaxMonoidal.δ Q _ _ ≫
        (Θ _ ⊗ₘ Θ _) ≫ Functor.LaxMonoidal.μ P₂ _ _ := by
    rw [← reassoc_of% (hΘ _ _), Functor.Monoidal.δ_μ, Category.comp_id]
  have hμ : F.map (adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F (S.obj B₁) (S.obj B₂) ≫
      (adj.counit.app B₁ ⊗ₘ adj.counit.app B₂))) ≫ adj.counit.app (B₁ ⊗ B₂) =
      Functor.OplaxMonoidal.δ F (S.obj B₁) (S.obj B₂) ≫
          (adj.counit.app B₁ ⊗ₘ adj.counit.app B₂) := by
    simp [Adjunction.homEquiv_unit]
  have hc := adj.counit.naturality e
  simp only [Functor.comp_map, Functor.id_map] at hc
  rw [Q.map_comp, Category.assoc, reassoc_of% (hnat _), ← P₂.map_comp, F.map_comp, Category.assoc,
    hc, ← Category.assoc (F.map _), hμ]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, ← Q.map_comp_assoc, Functor.Monoidal.μ_δ, Q.map_id, Category.id_comp,
    ← Functor.LaxMonoidal.μ_natural_assoc, ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rfl

lemma _root_.CategoryTheory.Adjunction.homEquiv_symm_comp_homEquiv {C D : Type*} [Category C]
    [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A B : C} {Z : D} (p : A ⟶ B)
    (e : F.obj B ⟶ Z) : (adj.homEquiv A Z).symm (p ≫ adj.homEquiv B Z e) = F.map p ≫ e := by
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]

section Pullback

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {V W X Y : Over (Spec (.of k))} [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
  [IsSeparated V.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

@[reassoc]
lemma upperStar_map_comp_eqToHom_congrArg {u u' : V ⟶ Y} (h : u = u') {M M' : Dᵇc(Y.left)⟦Λ⟧}
    (g : M ⟶ M') :
    (boundedConstructibleUpperStar Λ ℓ u).map g ≫
        eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj M') h) =
      eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj M) h) ≫
        (boundedConstructibleUpperStar Λ ℓ u').map g := by
  subst h
  simp

/-- The identification `Lq^* Lπ^* ≅ Lp^* Lf^*` of a commutative square `q ≫ π = p ≫ f` is
compatible with the tensor structures. -/
lemma upperStarComp_square_tensor_δ {q : V ⟶ W} {π : W ⟶ Y}
    {p : V ⟶ X} {f : X ⟶ Y}
    (w : q ≫ π = p ≫ f) (M₁ M₂ : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ q π).inv.app (M₁ ⊗ M₂) ≫
        eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            u).obj (M₁ ⊗ M₂)) w) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p f).hom.app (M₁ ⊗ M₂)
            ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p).map
          (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              f) M₁ M₂) ≫
        Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p)
            _ _ =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q).map
          (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              π) M₁ M₂) ≫
        Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ q)
            _ _ ≫
        (((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ q π).inv.app M₁ ≫
            eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj
                ℓ) ℓ u).obj M₁) w) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p f).hom.app M₁) ⊗ₘ
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ q π).inv.app M₂ ≫
            eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj
                ℓ) ℓ u).obj M₂) w) ≫
            (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p f).hom.app M₂))
                := by
  rw [← boundedConstructibleUpperStarComp_hom_app_tensor_δ,
    reassoc_of% (eqToHom_comp_δ_boundedConstructibleUpperStar ℓ w M₁ M₂),
    reassoc_of% (boundedConstructibleUpperStarComp_inv_app_tensor_δ ℓ q π M₁ M₂)]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom]

end Pullback

end AlgebraicGeometry.ProEtale.CondensedRing
