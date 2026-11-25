/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Mates of derived adjunctions and coefficient comparisons

This file contains the abstract diagram chases behind the compatibility of the derived base
change map with the restriction of scalars along a morphism of coefficient rings.

Consider two adjunctions `G ⊣ F` and `G' ⊣ F'` (think: over the coefficients `Λ` and `Λ'`),
"restriction" functors `P₁`, `P₂` from the primed to the unprimed categories and a square
`θ : P₁ ⋙ G ⟶ G' ⋙ P₂` whose mate is `κ : F' ⋙ P₁ ⟶ P₂ ⋙ F`. Suppose that the adjunctions are
derived to adjunctions `LG ⊣ RF` and `LG' ⊣ RF'` along localization functors, with units and
counits computed in terms of those of `G ⊣ F` and `G' ⊣ F'` (as for `Adjunction.derived`), and
let `τ : DP₁ ⋙ LG ⟶ LG' ⋙ DP₂` and `σ : RF' ⋙ DP₁ ⟶ DP₂ ⋙ RF` be squares of derived functors
induced by `θ` and `κ`. Then `σ` is the mate of `τ`
(`CategoryTheory.Adjunction.mateEquiv_eq_of_isRightDerivedFunctor`).

Second, the mate of a square of left adjoints is compatible with restriction functors as
soon as the square and the adjunctions are (`CategoryTheory.Adjunction.mateEquiv_restrict`).
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Adjunction

section Components

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- The components of the mate of a square. -/
lemma mateEquiv_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (d : D) :
    (mateEquiv adj₁ adj₂ α).app d =
      adj₂.unit.app (G.obj (R₁.obj d)) ≫ R₂.map (α.app (R₁.obj d)) ≫
        R₂.map (H.map (adj₁.counit.app d)) := by
  simp [mateEquiv_apply]

end Components

section DerivedMate

variable {C₁ C₂ C₁' C₂' D₁ D₂ D₁' D₂' : Type*} [Category C₁] [Category C₂] [Category C₁']
  [Category C₂'] [Category D₁] [Category D₂] [Category D₁'] [Category D₂']
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} {G' : C₁' ⥤ C₂'} {F' : C₂' ⥤ C₁'}
  {P₁ : C₁' ⥤ C₁} {P₂ : C₂' ⥤ C₂}
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₁' : C₁' ⥤ D₁'} {L₂' : C₂' ⥤ D₂'}
  {LG : D₁ ⥤ D₂} {RF : D₂ ⥤ D₁} {LG' : D₁' ⥤ D₂'} {RF' : D₂' ⥤ D₁'}
  {DP₁ : D₁' ⥤ D₁} {DP₂ : D₂' ⥤ D₂}

/-- The mate of a square `τ` of derived left adjoints, precomposed with the image of the unit
`β'` of the primed right derived functor, in terms of the underived mate `κ` of the underived
square `θ` inducing `τ`. -/
lemma map_app_mateEquiv_app (adj : G ⊣ F) (adj' : G' ⊣ F') (θ : P₁ ⋙ G ⟶ G' ⋙ P₂)
    (κ : F' ⋙ P₁ ⟶ P₂ ⋙ F)
    (hθκ : ∀ N, P₁.map (adj'.unit.app N) ≫ κ.app (G'.obj N) =
      adj.unit.app (P₁.obj N) ≫ F.map (θ.app N))
    (dadj : LG ⊣ RF) (dadj' : LG' ⊣ RF') (α : L₁ ⋙ LG ⟶ G ⋙ L₂) (β : F ⋙ L₁ ⟶ L₂ ⋙ RF)
    (α' : L₁' ⋙ LG' ⟶ G' ⋙ L₂') (β' : F' ⋙ L₁' ⟶ L₂' ⋙ RF')
    (hη : ∀ X, dadj.unit.app (L₁.obj X) ≫ RF.map (α.app X) =
      L₁.map (adj.unit.app X) ≫ β.app (G.obj X))
    (hε' : ∀ X, LG'.map (β'.app X) ≫ dadj'.counit.app (L₂'.obj X) =
      α'.app (F'.obj X) ≫ L₂'.map (adj'.counit.app X))
    (φ₁ : L₁' ⋙ DP₁ ≅ P₁ ⋙ L₁) (φ₂ : L₂' ⋙ DP₂ ≅ P₂ ⋙ L₂) (τ : DP₁ ⋙ LG ⟶ LG' ⋙ DP₂)
    (hτ : ∀ N, τ.app (L₁'.obj N) ≫ DP₂.map (α'.app N) ≫ φ₂.hom.app (G'.obj N) =
      LG.map (φ₁.hom.app N) ≫ α.app (P₁.obj N) ≫ L₂.map (θ.app N)) (X : C₂') :
    DP₁.map (β'.app X) ≫ (mateEquiv dadj' dadj τ).app (L₂'.obj X) =
      φ₁.hom.app (F'.obj X) ≫ L₁.map (κ.app X) ≫ β.app (P₂.obj X) ≫
        RF.map (φ₂.inv.app X) := by
  have h₀ := dadj.unit.naturality (DP₁.map (β'.app X))
  have h₁ := τ.naturality (β'.app X)
  have h₂ := φ₂.inv.naturality (adj'.counit.app X)
  have h₃ := β.naturality (θ.app (F'.obj X) ≫ P₂.map (adj'.counit.app X))
  have h₄ := κ.naturality (adj'.counit.app X)
  have h₅ := dadj.unit.naturality (φ₁.hom.app (F'.obj X))
  have h₆ := hτ (F'.obj X)
  have h₇ := hη (P₁.obj (F'.obj X))
  have h₈ := hθκ (F'.obj X)
  have h₉ := adj'.right_triangle_components X
  have h₁₀ := hε' X
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₀ h₁ h₂ h₃
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₄ h₅ h₆ h₇
  simp only [Functor.comp_obj, Functor.id_obj] at h₈ h₉ h₁₀ ⊢
  have h₆' : τ.app (L₁'.obj (F'.obj X)) ≫ DP₂.map (α'.app (F'.obj X)) =
      LG.map (φ₁.hom.app (F'.obj X)) ≫ α.app (P₁.obj (F'.obj X)) ≫
        L₂.map (θ.app (F'.obj X)) ≫ φ₂.inv.app (G'.obj (F'.obj X)) := by
    rw [← cancel_mono (φ₂.hom.app (G'.obj (F'.obj X)))]
    simpa using h₆
  calc DP₁.map (β'.app X) ≫ (mateEquiv dadj' dadj τ).app (L₂'.obj X)
      = dadj.unit.app (DP₁.obj (L₁'.obj (F'.obj X))) ≫
          RF.map (τ.app (L₁'.obj (F'.obj X)) ≫ DP₂.map (α'.app (F'.obj X)) ≫
            DP₂.map (L₂'.map (adj'.counit.app X))) := by
        rw [mateEquiv_app, reassoc_of% h₀, ← RF.map_comp, ← RF.map_comp, reassoc_of% h₁,
          ← DP₂.map_comp, h₁₀, DP₂.map_comp]
    _ = dadj.unit.app (DP₁.obj (L₁'.obj (F'.obj X))) ≫
          RF.map (LG.map (φ₁.hom.app (F'.obj X)) ≫ α.app (P₁.obj (F'.obj X)) ≫
            L₂.map (θ.app (F'.obj X) ≫ P₂.map (adj'.counit.app X)) ≫ φ₂.inv.app X) := by
        rw [reassoc_of% h₆', ← h₂, L₂.map_comp, Category.assoc]
    _ = φ₁.hom.app (F'.obj X) ≫ L₁.map (adj.unit.app (P₁.obj (F'.obj X)) ≫
          F.map (θ.app (F'.obj X) ≫ P₂.map (adj'.counit.app X))) ≫ β.app (P₂.obj X) ≫
            RF.map (φ₂.inv.app X) := by
        rw [RF.map_comp, ← reassoc_of% h₅, RF.map_comp, reassoc_of% h₇, RF.map_comp,
          ← reassoc_of% h₃, L₁.map_comp, Category.assoc]
    _ = _ := by
        rw [F.map_comp, ← Category.assoc (adj.unit.app _), ← h₈, Category.assoc, ← h₄,
          ← P₁.map_comp_assoc, h₉, P₁.map_id, Category.id_comp]

/-- **Mates of derived adjunctions.** Let `LG ⊣ RF` and `LG' ⊣ RF'` be adjunctions whose unit
and counit are induced by those of `G ⊣ F` and `G' ⊣ F'` through the localization functors, and
let `τ : DP₁ ⋙ LG ⟶ LG' ⋙ DP₂` be induced by `θ : P₁ ⋙ G ⟶ G' ⋙ P₂`. If `RF' ⋙ DP₁` is a right
derived functor whose unit factors through `DP₁` of the unit `β'` of `RF'`, then any
`σ : RF' ⋙ DP₁ ⟶ DP₂ ⋙ RF` induced by the mate `κ` of `θ` is the mate of `τ`. -/
lemma mateEquiv_eq_of_isRightDerivedFunctor (adj : G ⊣ F) (adj' : G' ⊣ F')
    (θ : P₁ ⋙ G ⟶ G' ⋙ P₂) (κ : F' ⋙ P₁ ⟶ P₂ ⋙ F)
    (hθκ : ∀ N, P₁.map (adj'.unit.app N) ≫ κ.app (G'.obj N) =
      adj.unit.app (P₁.obj N) ≫ F.map (θ.app N))
    (dadj : LG ⊣ RF) (dadj' : LG' ⊣ RF') (α : L₁ ⋙ LG ⟶ G ⋙ L₂) (β : F ⋙ L₁ ⟶ L₂ ⋙ RF)
    (α' : L₁' ⋙ LG' ⟶ G' ⋙ L₂') (β' : F' ⋙ L₁' ⟶ L₂' ⋙ RF')
    (hη : ∀ X, dadj.unit.app (L₁.obj X) ≫ RF.map (α.app X) =
      L₁.map (adj.unit.app X) ≫ β.app (G.obj X))
    (hε' : ∀ X, LG'.map (β'.app X) ≫ dadj'.counit.app (L₂'.obj X) =
      α'.app (F'.obj X) ≫ L₂'.map (adj'.counit.app X))
    (φ₁ : L₁' ⋙ DP₁ ≅ P₁ ⋙ L₁) (φ₂ : L₂' ⋙ DP₂ ≅ P₂ ⋙ L₂) (τ : DP₁ ⋙ LG ⟶ LG' ⋙ DP₂)
    (hτ : ∀ N, τ.app (L₁'.obj N) ≫ DP₂.map (α'.app N) ≫ φ₂.hom.app (G'.obj N) =
      LG.map (φ₁.hom.app N) ≫ α.app (P₁.obj N) ≫ L₂.map (θ.app N))
    (W : MorphismProperty C₂') [L₂'.IsLocalization W] {H₀ : C₂' ⥤ D₁}
    (β'' : H₀ ⟶ L₂' ⋙ RF' ⋙ DP₁) [(RF' ⋙ DP₁).IsRightDerivedFunctor β'' W]
    (hβ'' : ∀ X, ∃ e, β''.app X = e ≫ DP₁.map (β'.app X)) (σ : RF' ⋙ DP₁ ⟶ DP₂ ⋙ RF)
    (hσ : ∀ X, DP₁.map (β'.app X) ≫ σ.app (L₂'.obj X) =
      φ₁.hom.app (F'.obj X) ≫ L₁.map (κ.app X) ≫ β.app (P₂.obj X) ≫
        RF.map (φ₂.inv.app X)) :
    mateEquiv dadj' dadj τ = σ := by
  refine (RF' ⋙ DP₁).rightDerived_ext β'' W _ _ _ (NatTrans.ext (funext fun X ↦ ?_))
  obtain ⟨e, he⟩ := hβ'' X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, he, Category.assoc]
  rw [map_app_mateEquiv_app adj adj' θ κ hθκ dadj dadj' α β α' β' hη hε' φ₁ φ₂ τ hτ X, hσ]

end DerivedMate

section Restrict

variable {AY AX AY' AX' BY BX BY' BX' : Type*} [Category AY] [Category AX] [Category AY']
  [Category AX'] [Category BY] [Category BX] [Category BY'] [Category BX']
  {Lf : AY ⥤ AX} {Rf : AX ⥤ AY} {Lf' : AY' ⥤ AX'} {Rf' : AX' ⥤ AY'}
  {Lg : AY ⥤ AY'} {Lg' : AX ⥤ AX'}
  {Mf : BY ⥤ BX} {Sf : BX ⥤ BY} {Mf' : BY' ⥤ BX'} {Sf' : BX' ⥤ BY'}
  {Mg : BY ⥤ BY'} {Mg' : BX ⥤ BX'}
  {rY : BY ⥤ AY} {rX : BX ⥤ AX} {rY' : BY' ⥤ AY'} {rX' : BX' ⥤ AX'}

/-- **Mates and restriction functors.** Consider squares of left adjoints
`Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` and `Mg ⋙ Mf' ⟶ Mf ⋙ Mg'` related by restriction functors `r`, through
comparisons `τ` of the left adjoints and `σ` of the right adjoints, where each `σ` is the
mate of the corresponding `τ`. If the two squares are compatible with the comparisons, so are
their mates, the base change maps `Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` and `Sf ⋙ Mg ⟶ Mg' ⋙ Sf'`. -/
lemma mateEquiv_restrict (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (bdjf : Mf ⊣ Sf)
    (bdjf' : Mf' ⊣ Sf') (sqA : Lg ⋙ Lf' ⟶ Lf ⋙ Lg') (sqB : Mg ⋙ Mf' ⟶ Mf ⋙ Mg')
    (τf : rY ⋙ Lf ≅ Mf ⋙ rX) (σf : rX ⋙ Rf ≅ Sf ⋙ rY) (τf' : rY' ⋙ Lf' ≅ Mf' ⋙ rX')
    (σf' : rX' ⋙ Rf' ≅ Sf' ⋙ rY') (τg : rY ⋙ Lg ≅ Mg ⋙ rY') (τg' : rX ⋙ Lg' ≅ Mg' ⋙ rX')
    (hf : mateEquiv bdjf adjf τf.hom = σf.inv) (hf' : mateEquiv bdjf' adjf' τf'.hom = σf'.inv)
    (hsq : ∀ N, Lf'.map (τg.hom.app N) ≫ τf'.hom.app (Mg.obj N) ≫ rX'.map (sqB.app N) =
      sqA.app (rY.obj N) ≫ Lg'.map (τf.hom.app N) ≫ τg'.hom.app (Mf.obj N)) (K : BX) :
    Lg.map (σf.hom.app K) ≫ τg.hom.app (Sf.obj K) ≫ rY'.map ((mateEquiv bdjf bdjf' sqB).app K) =
      (mateEquiv adjf adjf' sqA).app (rX.obj K) ≫ Rf'.map (τg'.hom.app K) ≫
        σf'.hom.app (Mg'.obj K) := by
  have hu (c : BY') : rY'.map (bdjf'.unit.app c) =
      adjf'.unit.app (rY'.obj c) ≫ Rf'.map (τf'.hom.app c) ≫ σf'.hom.app (Mf'.obj c) := by
    have := unit_mateEquiv bdjf' adjf' τf'.hom c
    rw [hf'] at this
    simp only [Functor.comp_obj, Functor.id_obj] at this
    rw [← reassoc_of% this]
    simp
  have hc : τf.hom.app (Sf.obj K) ≫ rX.map (bdjf.counit.app K) =
      Lf.map (σf.inv.app K) ≫ adjf.counit.app (rX.obj K) := by
    have := mateEquiv_counit bdjf adjf τf.hom K
    rw [hf] at this
    exact this.symm
  have h₁ := σf'.hom.naturality (sqB.app (Sf.obj K) ≫ Mg'.map (bdjf.counit.app K))
  have h₂ := adjf'.unit.naturality (Lg.map (σf.hom.app K) ≫ τg.hom.app (Sf.obj K))
  have h₃ := sqA.naturality (σf.hom.app K)
  have h₄ := τg'.hom.naturality (bdjf.counit.app K)
  have h₅ := hsq (Sf.obj K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂ h₃ h₄
  calc Lg.map (σf.hom.app K) ≫ τg.hom.app (Sf.obj K) ≫
        rY'.map ((mateEquiv bdjf bdjf' sqB).app K)
      = adjf'.unit.app (Lg.obj (Rf.obj (rX.obj K))) ≫
          Rf'.map (Lf'.map (Lg.map (σf.hom.app K)) ≫ Lf'.map (τg.hom.app (Sf.obj K)) ≫
            τf'.hom.app (Mg.obj (Sf.obj K)) ≫ rX'.map (sqB.app (Sf.obj K)) ≫
            rX'.map (Mg'.map (bdjf.counit.app K))) ≫ σf'.hom.app (Mg'.obj K) := by
        rw [mateEquiv_app, rY'.map_comp, rY'.map_comp, hu]
        simp only [Category.assoc]
        rw [← rY'.map_comp, ← Sf'.map_comp, ← h₁, reassoc_of% h₂]
        simp only [Category.assoc, Functor.map_comp]
    _ = adjf'.unit.app (Lg.obj (Rf.obj (rX.obj K))) ≫
          Rf'.map (sqA.app (Rf.obj (rX.obj K)) ≫ Lg'.map (Lf.map (σf.hom.app K) ≫
            τf.hom.app (Sf.obj K) ≫ rX.map (bdjf.counit.app K)) ≫ τg'.hom.app K) ≫
          σf'.hom.app (Mg'.obj K) := by
        rw [reassoc_of% h₅, reassoc_of% h₃, ← h₄]
        simp only [Category.assoc, Functor.map_comp]
    _ = _ := by
        rw [hc, ← Lf.map_comp_assoc, Iso.hom_inv_id_app, mateEquiv_app]
        erw [CategoryTheory.Functor.map_id, Category.id_comp]
        simp only [Category.assoc, Functor.map_comp]

end Restrict
section Counit

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
  {L : A ⥤ A'} {R : A' ⥤ A} {M : B ⥤ B'} {S : B' ⥤ B} {rA : B ⥤ A} {rA' : B' ⥤ A'}

/-- If the comparison `σ` of right adjoints is the mate of the comparison `τ` of left adjoints,
then the comparisons are compatible with the counits. -/
lemma map_hom_app_comp_counit_of_mateEquiv (adj : L ⊣ R) (bdj : M ⊣ S)
    (τ : rA ⋙ L ≅ M ⋙ rA') (σ : rA' ⋙ R ≅ S ⋙ rA) (h : mateEquiv bdj adj τ.hom = σ.inv)
    (N : B') :
    L.map (σ.hom.app N) ≫ τ.hom.app (S.obj N) ≫ rA'.map (bdj.counit.app N) =
      adj.counit.app (rA'.obj N) := by
  have := mateEquiv_counit bdj adj τ.hom N
  rw [h] at this
  simp only [Functor.comp_obj] at this
  rw [← this, ← L.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end Counit

section Conjugate

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category B₁]
  [Category B₂] [Category B₃]
  {L₁ : A₂ ⥤ A₁} {R₁ : A₁ ⥤ A₂} {L₂ : A₃ ⥤ A₂} {R₂ : A₂ ⥤ A₃} {L : A₃ ⥤ A₁} {R : A₁ ⥤ A₃}
  {M₁ : B₂ ⥤ B₁} {S₁ : B₁ ⥤ B₂} {M₂ : B₃ ⥤ B₂} {S₂ : B₂ ⥤ B₃} {M : B₃ ⥤ B₁} {S : B₁ ⥤ B₃}
  {r₁ : B₁ ⥤ A₁} {r₂ : B₂ ⥤ A₂} {r₃ : B₃ ⥤ A₃}

/-- **Conjugates and restriction functors.** Let `L ⊣ R`, `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and their
primed versions `M ⊣ S`, `M₁ ⊣ S₁`, `M₂ ⊣ S₂` be related by restriction functors `r` through
comparisons `τ` of the left adjoints and `σ` of the right adjoints, each `σ` being the mate of
the corresponding `τ`. If the morphisms `L ⟶ L₂ ⋙ L₁` and `M ⟶ M₂ ⋙ M₁` are compatible with the
comparisons, so are their conjugates `R₁ ⋙ R₂ ⟶ R` and `S₁ ⋙ S₂ ⟶ S`. -/
lemma conjugateEquiv_comp_restrict (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R) (b₁ : M₁ ⊣ S₁)
    (b₂ : M₂ ⊣ S₂) (b : M ⊣ S) (τ₁ : r₂ ⋙ L₁ ≅ M₁ ⋙ r₁) (σ₁ : r₁ ⋙ R₁ ≅ S₁ ⋙ r₂)
    (τ₂ : r₃ ⋙ L₂ ≅ M₂ ⋙ r₂) (σ₂ : r₂ ⋙ R₂ ≅ S₂ ⋙ r₃) (τ : r₃ ⋙ L ≅ M ⋙ r₁)
    (σ : r₁ ⋙ R ≅ S ⋙ r₃) (h₁ : mateEquiv b₁ a₁ τ₁.hom = σ₁.inv)
    (h₂ : mateEquiv b₂ a₂ τ₂.hom = σ₂.inv) (h : mateEquiv b a τ.hom = σ.inv)
    (eL : L ⟶ L₂ ⋙ L₁) (eM : M ⟶ M₂ ⋙ M₁)
    (he : ∀ N, τ.hom.app N ≫ r₁.map (eM.app N) =
      eL.app (r₃.obj N) ≫ L₁.map (τ₂.hom.app N) ≫ τ₁.hom.app (M₂.obj N)) (X : B₁) :
    R₂.map (σ₁.hom.app X) ≫ σ₂.hom.app (S₁.obj X) ≫
        r₃.map ((conjugateEquiv (b₂.comp b₁) b eM).app X) =
      (conjugateEquiv (a₂.comp a₁) a eL).app (r₁.obj X) ≫ σ.hom.app X := by
  rw [← cancel_mono (σ.inv.app X)]
  simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have k₁ := map_hom_app_comp_counit_of_mateEquiv a₁ b₁ τ₁ σ₁ h₁ X
  have k₂ := map_hom_app_comp_counit_of_mateEquiv a₂ b₂ τ₂ σ₂ h₂ (S₁.obj X)
  have k := mateEquiv_counit b a τ.hom X
  rw [h] at k
  have c := conjugateEquiv_counit (b₂.comp b₁) b eM X
  have c' := conjugateEquiv_counit (a₂.comp a₁) a eL (r₁.obj X)
  have n₁ := τ.hom.naturality ((conjugateEquiv (b₂.comp b₁) b eM).app X)
  have n₂ := eL.naturality (R₂.map (σ₁.hom.app X) ≫ σ₂.hom.app (S₁.obj X))
  have n₃ := τ₁.hom.naturality (b₂.counit.app (S₁.obj X))
  have n₄ := a₂.counit.naturality (σ₁.hom.app X)
  have e₀ := he (S₂.obj (S₁.obj X))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    comp_counit_app] at k₁ k₂ k c c' n₁ n₂ n₃ n₄ e₀
  rw [k, reassoc_of% n₁, ← r₁.map_comp, c, r₁.map_comp, reassoc_of% e₀, c', ← L.map_comp_assoc,
    reassoc_of% n₂, Functor.map_comp, ← L₁.map_comp_assoc, r₁.map_comp, ← reassoc_of% n₃,
    ← L₁.map_comp_assoc]
  simp only [Category.assoc]
  rw [k₂, n₄, L₁.map_comp, Category.assoc, k₁]

end Conjugate
section Comparison

variable {AX Ac Ad AY BX Bc Bd BY : Type*} [Category AX] [Category Ac] [Category Ad]
  [Category AY] [Category BX] [Category Bc] [Category Bd] [Category BY]
  {Jc : AX ⥤ Ac} {Jd : AX ⥤ Ad} {Q : Ad ⥤ Ac} {Rq : Ac ⥤ Ad} {Rdg : Ad ⥤ AY} {Rcg : Ac ⥤ AY}
  {Jc' : BX ⥤ Bc} {Jd' : BX ⥤ Bd} {Q' : Bd ⥤ Bc} {Rq' : Bc ⥤ Bd} {Rdg' : Bd ⥤ BY}
  {Rcg' : Bc ⥤ BY} {rX : BX ⥤ AX} {rc : Bc ⥤ Ac} {rd : Bd ⥤ Ad} {rY : BY ⥤ AY}

/-- **Comparison maps along a refinement and restriction functors.** The composite
`Jd ⋙ Rdg ⟶ Jd ⋙ Q ⋙ Rq ⋙ Rdg ≅ Jc ⋙ Rq ⋙ Rdg ≅ Jc ⋙ Rcg` of the unit of `Q ⊣ Rq`, the inverse
of an isomorphism `bc : Jc ≅ Jd ⋙ Q` and an isomorphism `comp : Rq ⋙ Rdg ≅ Rcg` is compatible
with comparisons along restriction functors as soon as `bc` and `comp` are, and the comparison
`σq` of `Rq` is the mate of the comparison `τq` of `Q`. -/
lemma comparison_restrict (adj : Q ⊣ Rq) (adj' : Q' ⊣ Rq') (bc : Jc ≅ Jd ⋙ Q)
    (bc' : Jc' ≅ Jd' ⋙ Q') (comp : Rq ⋙ Rdg ≅ Rcg) (comp' : Rq' ⋙ Rdg' ≅ Rcg')
    (ιc : rX ⋙ Jc ≅ Jc' ⋙ rc) (ιd : rX ⋙ Jd ≅ Jd' ⋙ rd) (τq : rd ⋙ Q ≅ Q' ⋙ rc)
    (σq : rc ⋙ Rq ≅ Rq' ⋙ rd) (σdg : rd ⋙ Rdg ≅ Rdg' ⋙ rY) (σcg : rc ⋙ Rcg ≅ Rcg' ⋙ rY)
    (hq : mateEquiv adj' adj τq.hom = σq.inv)
    (hbc : ∀ K, ιc.hom.app K ≫ rc.map (bc'.hom.app K) =
      bc.hom.app (rX.obj K) ≫ Q.map (ιd.hom.app K) ≫ τq.hom.app (Jd'.obj K))
    (hcomp : ∀ M, Rdg.map (σq.hom.app M) ≫ σdg.hom.app (Rq'.obj M) ≫ rY.map (comp'.hom.app M) =
      comp.hom.app (rc.obj M) ≫ σcg.hom.app M) (K : BX) :
    (Rdg.map (ιd.hom.app K) ≫ σdg.hom.app (Jd'.obj K)) ≫
        rY.map ((Functor.whiskerRight (Functor.whiskerLeft Jd' adj'.unit) Rdg' ≫
          Functor.whiskerRight bc'.inv (Rq' ⋙ Rdg') ≫
          Functor.whiskerLeft Jc' comp'.hom).app K) =
      (Functor.whiskerRight (Functor.whiskerLeft Jd adj.unit) Rdg ≫
          Functor.whiskerRight bc.inv (Rq ⋙ Rdg) ≫ Functor.whiskerLeft Jc comp.hom).app
          (rX.obj K) ≫ Rcg.map (ιc.hom.app K) ≫ σcg.hom.app (Jc'.obj K) := by
  have hu (c : Bd) : rd.map (adj'.unit.app c) =
      adj.unit.app (rd.obj c) ≫ Rq.map (τq.hom.app c) ≫ σq.hom.app (Q'.obj c) := by
    have := unit_mateEquiv adj' adj τq.hom c
    rw [hq] at this
    simp only [Functor.comp_obj, Functor.id_obj] at this
    rw [← reassoc_of% this]
    simp
  have hbc' : Q.map (ιd.hom.app K) ≫ τq.hom.app (Jd'.obj K) ≫ rc.map (bc'.inv.app K) =
      bc.inv.app (rX.obj K) ≫ ιc.hom.app K := by
    rw [← cancel_epi (bc.hom.app (rX.obj K)), ← reassoc_of% (hbc K)]
    simp [← Functor.map_comp]
  have n₁ := σdg.hom.naturality (adj'.unit.app (Jd'.obj K) ≫ Rq'.map (bc'.inv.app K))
  have n₂ := σq.hom.naturality (bc'.inv.app K)
  have n₃ := adj.unit.naturality (ιd.hom.app K)
  have n₄ := comp.hom.naturality (ιc.hom.app K)
  have h₅ := hcomp (Jc'.obj K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n₁ n₂ n₃ n₄
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc]
  calc Rdg.map (ιd.hom.app K) ≫ σdg.hom.app (Jd'.obj K) ≫
        rY.map (Rdg'.map (adj'.unit.app (Jd'.obj K))) ≫
        rY.map (Rdg'.map (Rq'.map (bc'.inv.app K))) ≫ rY.map (comp'.hom.app (Jc'.obj K))
      = Rdg.map (adj.unit.app (Jd.obj (rX.obj K)) ≫ Rq.map (Q.map (ιd.hom.app K) ≫
          τq.hom.app (Jd'.obj K) ≫ rc.map (bc'.inv.app K)) ≫ σq.hom.app (Jc'.obj K)) ≫
          σdg.hom.app (Rq'.obj (Jc'.obj K)) ≫ rY.map (comp'.hom.app (Jc'.obj K)) := by
        have n₂' := Rdg.congr_map n₂
        have n₃' := Rdg.congr_map n₃
        simp only [Functor.map_comp, Category.assoc] at n₁ n₂' n₃' ⊢
        rw [← reassoc_of% n₁, hu]
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% n₃', reassoc_of% n₂']
    _ = _ := by
        rw [hbc']
        simp only [Functor.map_comp, Category.assoc]
        rw [h₅, reassoc_of% n₄]

end Comparison

end CategoryTheory.Adjunction
