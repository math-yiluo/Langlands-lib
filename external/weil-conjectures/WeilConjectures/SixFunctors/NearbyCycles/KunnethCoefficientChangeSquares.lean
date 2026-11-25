/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-!

# Commutative squares for the change of coefficients of the Künneth map

This file contains the formal (abstract) parts of the compatibility of the Künneth map of nearby
cycles with a change of coefficients `c` (an extension of scalars): `c` is given on every category
involved, together with isomorphisms `P : L ⋙ c ≅ c ⋙ L'` for the left adjoints (derived
pullbacks), comparisons `ρ : J ⋙ c ⟶ c ⋙ J'` for the right adjoints (derived pushforwards) and
tensor comparisons `m : c (a ⊗ b) ⟶ c a ⊗ c b`.

* `CategoryTheory.Adjunction.map_homEquiv_comp_mateEquiv_app`: the mate `ρ` of `P⁻¹` is
  compatible with the lax tensor maps `G A ⊗ G B ⟶ G (A ⊗ B)` of the right adjoints, adjoint to
  the tensor product of the counits, if `P` is compatible with the oplax structures of the left
  adjoints.
* `CategoryTheory.map_μ_comp_of_map_δ_comp`: the compatibility of `P` with the oplax structures
  `δ` of strong monoidal functors gives the compatibility with their lax structures `μ`.
* `CategoryTheory.map_laxComp_comp_eq`: the lax tensor map `μ_I ≫ I (μ_J ≫ J μ_E)` of a composite
  `I ∘ J ∘ E` (the lax tensor map of nearby cycles) is compatible with `c`.
* `CategoryTheory.map_exchange_comp_eq`: an exchange `I_N ⋙ F' ⟶ T ⋙ I_M` pasted with
  `J_N ⋙ T ⟶ G ⋙ J_M` and `E_N ⋙ G ⟶ F ⋙ E_M` (the pullback exchange of nearby cycles) is
  compatible with `c`, if the three pieces are.
* `CategoryTheory.map_tensorHom_comp_comp_eq`: the tensor product of two such squares, followed
  by a compatible lax map (the Künneth map).

-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

section LaxRightAdjoint

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
  {N_D : D ⥤ D'} {N_C : C ⥤ C'} (α : N_D ⋙ F' ≅ F ⋙ N_C)

/-- **The mate of a monoidal comparison and the lax tensor maps of right adjoints.** Let
`α : N_D ⋙ F' ≅ F ⋙ N_C` be compatible with comparisons `δF : F (a ⊗ b) ⟶ F a ⊗ F b`,
`δF'`, `m_C`, `m_D`. Then the mate `β : G ⋙ N_D ⟶ N_C ⋙ G'` of `α` is compatible with the lax
tensor maps `G A ⊗ G B ⟶ G (A ⊗ B)`, the adjoints of `δF ≫ (ε ⊗ ε)`, and their analogues for
`G'`. -/
lemma Adjunction.map_homEquiv_comp_mateEquiv_app
    (δF : ∀ a b : D, F.obj (a ⊗ b) ⟶ F.obj a ⊗ F.obj b)
    (δF' : ∀ a b : D', F'.obj (a ⊗ b) ⟶ F'.obj a ⊗ F'.obj b)
    (hδF' : ∀ {a a' b b' : D'} (x : a ⟶ a') (y : b ⟶ b'),
      F'.map (x ⊗ₘ y) ≫ δF' a' b' = δF' a b ≫ (F'.map x ⊗ₘ F'.map y))
    (mC : ∀ a b : C, N_C.obj (a ⊗ b) ⟶ N_C.obj a ⊗ N_C.obj b)
    (hmC : ∀ {a a' b b' : C} (x : a ⟶ a') (y : b ⟶ b'),
      N_C.map (x ⊗ₘ y) ≫ mC a' b' = mC a b ≫ (N_C.map x ⊗ₘ N_C.map y))
    (mD : ∀ a b : D, N_D.obj (a ⊗ b) ⟶ N_D.obj a ⊗ N_D.obj b)
    (H : ∀ a b : D, N_C.map (δF a b) ≫ mC (F.obj a) (F.obj b) =
      α.inv.app (a ⊗ b) ≫ F'.map (mD a b) ≫ δF' (N_D.obj a) (N_D.obj b) ≫
        (α.hom.app a ⊗ₘ α.hom.app b))
    (A B : C) :
    N_D.map (adj.homEquiv _ _ (δF (G.obj A) (G.obj B) ≫
        (adj.counit.app A ⊗ₘ adj.counit.app B))) ≫
        (mateEquiv adj adj' α.hom).app (A ⊗ B) ≫ G'.map (mC A B) =
      mD (G.obj A) (G.obj B) ≫
        ((mateEquiv adj adj' α.hom).app A ⊗ₘ (mateEquiv adj adj' α.hom).app B) ≫
        adj'.homEquiv _ _ (δF' (G'.obj (N_C.obj A)) (G'.obj (N_C.obj B)) ≫
          (adj'.counit.app (N_C.obj A) ⊗ₘ adj'.counit.app (N_C.obj B))) := by
  apply (adj'.homEquiv _ _).symm.injective
  have hβ (X : C) : F'.map ((mateEquiv adj adj' α.hom).app X) ≫ adj'.counit.app (N_C.obj X) =
      α.hom.app (G.obj X) ≫ N_C.map (adj.counit.app X) :=
    mateEquiv_counit adj adj' α.hom X
  have hc' {X : D'} {Y : C'} (g : F'.obj X ⟶ Y) :
      F'.map (adj'.homEquiv _ _ g) ≫ adj'.counit.app Y = g :=
    (adj'.homEquiv_counit (g := _)).symm.trans ((adj'.homEquiv _ _).symm_apply_apply _)
  have hμ : F.map (adj.homEquiv (G.obj A ⊗ G.obj B) (A ⊗ B) (δF (G.obj A) (G.obj B) ≫
      (adj.counit.app A ⊗ₘ adj.counit.app B))) ≫ adj.counit.app (A ⊗ B) =
      δF (G.obj A) (G.obj B) ≫ (adj.counit.app A ⊗ₘ adj.counit.app B) :=
    (adj.homEquiv_counit (g := _)).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)
  have hα := α.hom.naturality (adj.homEquiv _ _ (δF (G.obj A) (G.obj B) ≫
      (adj.counit.app A ⊗ₘ adj.counit.app B)))
  simp only [Functor.comp_map, Functor.comp_obj] at hα
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality]
  rw [reassoc_of% (hβ (A ⊗ B))]
  erw [reassoc_of% hα]
  rw [← N_C.map_comp_assoc]
  erw [hμ]
  rw [N_C.map_comp, Category.assoc]
  erw [hmC]
  rw [reassoc_of% (H (G.obj A) (G.obj B)), Iso.hom_inv_id_app_assoc]
  erw [hc', reassoc_of% (hδF' _ _)]
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hβ, hβ]

end LaxRightAdjoint

section Monoidal

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']

/-- The compatibility of an isomorphism `P : F ⋙ N_C ≅ N_D ⋙ F'` with the comonoidal structures
`δ` of strong monoidal functors `F`, `F'` and comparisons `m_C`, `m_D` gives the compatibility
with their monoidal structures `μ`. -/
lemma map_μ_comp_of_map_δ_comp {F : D ⥤ C} {F' : D' ⥤ C'} [F.Monoidal] [F'.Monoidal]
    {N_D : D ⥤ D'} {N_C : C ⥤ C'} (P : F ⋙ N_C ≅ N_D ⋙ F')
    (mC : ∀ a b : C, N_C.obj (a ⊗ b) ⟶ N_C.obj a ⊗ N_C.obj b)
    (mD : ∀ a b : D, N_D.obj (a ⊗ b) ⟶ N_D.obj a ⊗ N_D.obj b)
    (H : ∀ a b : D, N_C.map (Functor.OplaxMonoidal.δ F a b) ≫ mC (F.obj a) (F.obj b) =
      P.hom.app (a ⊗ b) ≫ F'.map (mD a b) ≫ Functor.OplaxMonoidal.δ F' _ _ ≫
        (P.inv.app a ⊗ₘ P.inv.app b))
    (a b : D) :
    mC (F.obj a) (F.obj b) ≫ (P.hom.app a ⊗ₘ P.hom.app b) ≫ Functor.LaxMonoidal.μ F' _ _ =
      N_C.map (Functor.LaxMonoidal.μ F a b) ≫ P.hom.app (a ⊗ b) ≫ F'.map (mD a b) := by
  rw [← cancel_epi (N_C.map (Functor.OplaxMonoidal.δ F a b)), reassoc_of% (H a b)]
  simp [← Functor.map_comp_assoc]

end Monoidal

section LaxComp

variable {DX DG DT DS DX' DG' DT' DS' : Type*} [Category* DX] [Category* DG] [Category* DT]
  [Category* DS] [Category* DX'] [Category* DG'] [Category* DT'] [Category* DS']
  [MonoidalCategory DX] [MonoidalCategory DG] [MonoidalCategory DT] [MonoidalCategory DS]
  [MonoidalCategory DX'] [MonoidalCategory DG'] [MonoidalCategory DT'] [MonoidalCategory DS']
  {E : DX ⥤ DG} {J : DG ⥤ DT} {I : DT ⥤ DS} {E' : DX' ⥤ DG'} {J' : DG' ⥤ DT'} {I' : DT' ⥤ DS'}
  {cX : DX ⥤ DX'} {cG : DG ⥤ DG'} {cT : DT ⥤ DT'} {cS : DS ⥤ DS'}

/-- **The lax tensor map of a composite and a change of coefficients.** Let `I ∘ J ∘ E` be a
composite of functors with lax tensor maps `μ_E`, `μ_J`, `μ_I`, and `c` functors relating it to
`I' ∘ J' ∘ E'`, with comparisons `P_E : E ⋙ c ≅ c ⋙ E'`, `P_I`, `ρ : J ⋙ c ⟶ c ⋙ J'` and tensor
comparisons `m`, all compatible with the lax tensor maps. Then the lax tensor map
`μ_I ≫ I (μ_J ≫ J μ_E)` of the composite is compatible with
`Φ = P_I ≫ I' (ρ ≫ J' P_E) : c (I J E U) ⟶ I' J' E' (c U)`. -/
lemma map_laxComp_comp_eq (PE : E ⋙ cG ≅ cX ⋙ E') (PI : I ⋙ cS ≅ cT ⋙ I')
    (ρ : J ⋙ cT ⟶ cG ⋙ J')
    (μE : ∀ a b : DX, E.obj a ⊗ E.obj b ⟶ E.obj (a ⊗ b))
    (μE' : ∀ a b : DX', E'.obj a ⊗ E'.obj b ⟶ E'.obj (a ⊗ b))
    (μJ : ∀ a b : DG, J.obj a ⊗ J.obj b ⟶ J.obj (a ⊗ b))
    (μJ' : ∀ a b : DG', J'.obj a ⊗ J'.obj b ⟶ J'.obj (a ⊗ b))
    (μI : ∀ a b : DT, I.obj a ⊗ I.obj b ⟶ I.obj (a ⊗ b))
    (μI' : ∀ a b : DT', I'.obj a ⊗ I'.obj b ⟶ I'.obj (a ⊗ b))
    (hμJ' : ∀ {a a' b b' : DG'} (x : a ⟶ a') (y : b ⟶ b'),
      (J'.map x ⊗ₘ J'.map y) ≫ μJ' a' b' = μJ' a b ≫ J'.map (x ⊗ₘ y))
    (hμI' : ∀ {a a' b b' : DT'} (x : a ⟶ a') (y : b ⟶ b'),
      (I'.map x ⊗ₘ I'.map y) ≫ μI' a' b' = μI' a b ≫ I'.map (x ⊗ₘ y))
    (mX : ∀ a b : DX, cX.obj (a ⊗ b) ⟶ cX.obj a ⊗ cX.obj b)
    (mG : ∀ a b : DG, cG.obj (a ⊗ b) ⟶ cG.obj a ⊗ cG.obj b)
    (mT : ∀ a b : DT, cT.obj (a ⊗ b) ⟶ cT.obj a ⊗ cT.obj b)
    (mS : ∀ a b : DS, cS.obj (a ⊗ b) ⟶ cS.obj a ⊗ cS.obj b)
    (hE : ∀ a b : DX, mG (E.obj a) (E.obj b) ≫ (PE.hom.app a ⊗ₘ PE.hom.app b) ≫
      μE' (cX.obj a) (cX.obj b) = cG.map (μE a b) ≫ PE.hom.app (a ⊗ b) ≫ E'.map (mX a b))
    (hJ : ∀ a b : DG, mT (J.obj a) (J.obj b) ≫ (ρ.app a ⊗ₘ ρ.app b) ≫
      μJ' (cG.obj a) (cG.obj b) = cT.map (μJ a b) ≫ ρ.app (a ⊗ b) ≫ J'.map (mG a b))
    (hI : ∀ a b : DT, mS (I.obj a) (I.obj b) ≫ (PI.hom.app a ⊗ₘ PI.hom.app b) ≫
      μI' (cT.obj a) (cT.obj b) = cS.map (μI a b) ≫ PI.hom.app (a ⊗ b) ≫ I'.map (mT a b))
    (U V : DX) :
    cS.map (μI _ _ ≫ I.map (μJ _ _ ≫ J.map (μE U V))) ≫
        (PI.hom.app _ ≫ I'.map (ρ.app _ ≫ J'.map (PE.hom.app (U ⊗ V)))) ≫
        I'.map (J'.map (E'.map (mX U V))) =
      mS _ _ ≫ ((PI.hom.app _ ≫ I'.map (ρ.app _ ≫ J'.map (PE.hom.app U))) ⊗ₘ
          (PI.hom.app _ ≫ I'.map (ρ.app _ ≫ J'.map (PE.hom.app V)))) ≫
        μI' _ _ ≫ I'.map (μJ' _ _ ≫ J'.map (μE' _ _)) := by
  have key : cT.map (μJ _ _ ≫ J.map (μE U V)) ≫ ρ.app (E.obj (U ⊗ V)) ≫
      J'.map (PE.hom.app (U ⊗ V)) ≫ J'.map (E'.map (mX U V)) =
      mT _ _ ≫ ((ρ.app _ ≫ J'.map (PE.hom.app U)) ⊗ₘ (ρ.app _ ≫ J'.map (PE.hom.app V))) ≫
        μJ' _ _ ≫ J'.map (μE' _ _) := by
    have hρ := ρ.naturality (μE U V)
    have hE' := congrArg J'.map (hE U V)
    simp only [Functor.comp_map, Functor.map_comp] at hρ hE'
    simp only [Functor.map_comp, Category.assoc, ← tensorHom_comp_tensorHom]
    rw [reassoc_of% hρ, ← hE', ← reassoc_of% (hJ _ _), reassoc_of% (hμJ' _ _)]
  have hP := PI.hom.naturality (μJ _ _ ≫ J.map (μE U V))
  have key' := congrArg I'.map key
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hP key'
  simp only [Functor.map_comp, Category.assoc, ← tensorHom_comp_tensorHom]
  rw [reassoc_of% hP, key', reassoc_of% (hμI' _ _), ← reassoc_of% (hI _ _)]
  simp only [← I'.map_comp, ← tensorHom_comp_tensorHom, Category.assoc]
  rw [reassoc_of% (hμI' _ _)]
  simp only [Functor.map_comp]

end LaxComp
section Exchange

/-- Inverting the isomorphisms in a commutative square of isomorphisms and morphisms. -/
private lemma comp_hom_hom_eq_of_inv_inv_comp {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (i₁ : O₂ ≅ O₁) (i₂ : O₃ ≅ O₂) (x : O₃ ⟶ O₄) (y : O₁ ⟶ O₅) (j₁ : O₆ ≅ O₅) (j₂ : O₄ ≅ O₆)
    (h : i₁.inv ≫ i₂.inv ≫ x = y ≫ j₁.inv ≫ j₂.inv) :
    x ≫ j₂.hom ≫ j₁.hom = i₂.hom ≫ i₁.hom ≫ y := by
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq] at h
  rw [h]
  simp

/-- Inverting the isomorphisms in a commutative square of two isomorphisms and morphisms. -/
private lemma comp_comp_hom_eq_of_inv_comp {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (i : O₂ ≅ O₁) (x : O₂ ⟶ O₃) (y : O₃ ⟶ O₄) (u : O₁ ⟶ O₅) (v : O₅ ⟶ O₆) (j : O₄ ≅ O₆)
    (h : i.inv ≫ x ≫ y = u ≫ v ≫ j.inv) :
    x ≫ y ≫ j.hom = i.hom ≫ u ≫ v := by
  rw [Iso.inv_comp_eq] at h
  rw [reassoc_of% h]
  simp

variable {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category* DY'] [Category* DX'] [Category* DTN]
  [Category* DTM] [Category* DGN] [Category* DGM] [Category* DY] [Category* DX]
  {EY' EX' ETN ETM EGN EGM EY EX : Type*} [Category* EY'] [Category* EX'] [Category* ETN]
  [Category* ETM] [Category* EGN] [Category* EGM] [Category* EY] [Category* EX]
  {Fp : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
  {JN : DGN ⥤ DTN} {JM : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
  {F : DY ⥤ DX}
  {Fp' : EY' ⥤ EX'} {IN' : ETN ⥤ EY'} {IM' : ETM ⥤ EX'} {T' : ETN ⥤ ETM}
  {JN' : EGN ⥤ ETN} {JM' : EGM ⥤ ETM} {G' : EGN ⥤ EGM} {EN' : EY ⥤ EGN} {EM' : EX ⥤ EGM}
  {F' : EY ⥤ EX}
  {cY' : DY' ⥤ EY'} {cX' : DX' ⥤ EX'} {cTN : DTN ⥤ ETN} {cTM : DTM ⥤ ETM} {cGN : DGN ⥤ EGN}
  {cGM : DGM ⥤ EGM} {cY : DY ⥤ EY} {cX : DX ⥤ EX}

/-- **The pullback exchange of nearby cycles and a change of coefficients.** The exchange
`θ_i ≫ I_M (β ≫ J_M θ_ε) : F_p (I_N J_N E_N A) ⟶ I_M J_M E_M (F A)` pasted from three
exchanges is compatible with the change of coefficients `c`, through the comparisons
`Φ = P_I ≫ I' (ρ ≫ J' P_E) : c (I J E A) ⟶ I' J' E' (c A)`, if the three exchanges are: `θ_i`
and `θ_ε` in the form of the cube condition of `CategoryTheory.mateEquiv_app_cube` for the
isomorphisms `P` (inverted), and `β` in the form of its conclusion. -/
lemma map_exchange_comp_eq
    (θi : IN ⋙ Fp ⟶ T ⋙ IM) (β : JN ⋙ T ⟶ G ⋙ JM) (θε : EN ⋙ G ⟶ F ⋙ EM)
    (θi' : IN' ⋙ Fp' ⟶ T' ⋙ IM') (β' : JN' ⋙ T' ⟶ G' ⋙ JM') (θε' : EN' ⋙ G' ⟶ F' ⋙ EM')
    (PFp : Fp ⋙ cX' ≅ cY' ⋙ Fp') (PIN : IN ⋙ cY' ≅ cTN ⋙ IN') (PIM : IM ⋙ cX' ≅ cTM ⋙ IM')
    (PT : T ⋙ cTM ≅ cTN ⋙ T') (PG : G ⋙ cGM ≅ cGN ⋙ G') (PEN : EN ⋙ cGN ≅ cY ⋙ EN')
    (PEM : EM ⋙ cGM ≅ cX ⋙ EM') (PF : F ⋙ cX ≅ cY ⋙ F')
    (ρN : JN ⋙ cTN ⟶ cGN ⋙ JN') (ρM : JM ⋙ cTM ⟶ cGM ⋙ JM')
    (hθi : ∀ o, Fp'.map (PIN.inv.app o) ≫ PFp.inv.app (IN.obj o) ≫ cX'.map (θi.app o) =
      θi'.app (cTN.obj o) ≫ IM'.map (PT.inv.app o) ≫ PIM.inv.app (T.obj o))
    (hβ : ∀ o, PT.inv.app (JN.obj o) ≫ cTM.map (β.app o) ≫ ρM.app (G.obj o) =
      T'.map (ρN.app o) ≫ β'.app (cGN.obj o) ≫ JM'.map (PG.inv.app o))
    (hθε : ∀ o, G'.map (PEN.inv.app o) ≫ PG.inv.app (EN.obj o) ≫ cGM.map (θε.app o) =
      θε'.app (cY.obj o) ≫ EM'.map (PF.inv.app o) ≫ PEM.inv.app (F.obj o))
    (α : (EN ⋙ JN ⋙ IN) ⋙ Fp ⟶ F ⋙ EM ⋙ JM ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JN) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε JM) IM)
    (α' : (EN' ⋙ JN' ⋙ IN') ⋙ Fp' ⟶ F' ⋙ EM' ⋙ JM' ⋙ IM')
    (hα' : α' = Functor.whiskerLeft (EN' ⋙ JN') θi' ≫
      Functor.whiskerRight (Functor.whiskerLeft EN' β' ≫ Functor.whiskerRight θε' JM') IM')
    (A : DY) :
    cX'.map (α.app A) ≫
        (PIM.hom.app _ ≫ IM'.map (ρM.app _ ≫ JM'.map (PEM.hom.app (F.obj A)))) ≫
        IM'.map (JM'.map (EM'.map (PF.hom.app A))) =
      PFp.hom.app _ ≫ Fp'.map (PIN.hom.app _ ≫ IN'.map (ρN.app _ ≫ JN'.map (PEN.hom.app A))) ≫
        α'.app (cY.obj A) := by
  subst hα hα'
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hθi' := comp_hom_hom_eq_of_inv_inv_comp (Fp'.mapIso (PIN.app (JN.obj (EN.obj A))))
    (PFp.app _) _ _ (IM'.mapIso (PT.app _)) (PIM.app _) (hθi (JN.obj (EN.obj A)))
  have hβ' := congrArg IM'.map (comp_comp_hom_eq_of_inv_comp (PT.app _) _ _ _ _
    (JM'.mapIso (PG.app _)) (hβ (EN.obj A)))
  have hθε' := congrArg (fun x ↦ IM'.map (JM'.map x)) (comp_hom_hom_eq_of_inv_inv_comp
    (G'.mapIso (PEN.app A)) (PG.app _) _ _ (EM'.mapIso (PF.app A)) (PEM.app _) (hθε A))
  have n₁ := PIM.hom.naturality (β.app (EN.obj A) ≫ JM.map (θε.app A))
  have n₂ := congrArg IM'.map (ρM.naturality (θε.app A))
  have n₃ := θi'.naturality (ρN.app (EN.obj A) ≫ JN'.map (PEN.hom.app A))
  have n₄ := congrArg IM'.map (β'.naturality (PEN.hom.app A))
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc, Functor.mapIso_hom,
    Iso.app_hom, Functor.comp_obj] at hθi' hβ' hθε' n₁ n₂ n₃ n₄
  simp only [Functor.map_comp, Category.assoc, Functor.comp_obj]
  rw [reassoc_of% n₁, reassoc_of% n₂, hθε', reassoc_of% hβ', reassoc_of% hθi', reassoc_of% n₃,
    reassoc_of% n₄]

end Exchange

/-- Two morphisms related by a commutative square with invertible sides are isomorphic arrows. -/
lemma nonempty_arrowIso_of_comp_eq {C : Type*} [Category* C] {A B A' B' : C} {f : A ⟶ B}
    {g : A' ⟶ B'} {e₁ : A ⟶ A'} {e₂ : B ⟶ B'} (h : f ≫ e₂ = e₁ ≫ g) (he₁ : IsIso e₁)
    (he₂ : IsIso e₂) : Nonempty (Arrow.mk f ≅ Arrow.mk g) :=
  ⟨Arrow.isoMk' f g (asIso e₁) (asIso e₂) h.symm⟩

section Tensor

variable {C C' : Type*} [Category* C] [Category* C'] [MonoidalCategory C] [MonoidalCategory C']

/-- **The Künneth square.** If `c` carries `a₁`, `a₂` and `μ` to `a₁'`, `a₂'` and `μ'` (up to the
tensor comparison `m` of `c`), then it carries `(a₁ ⊗ a₂) ≫ μ` to `(a₁' ⊗ a₂') ≫ μ'`. -/
lemma map_tensorHom_comp_comp_eq (c : C ⥤ C')
    (m : ∀ a b : C, c.obj (a ⊗ b) ⟶ c.obj a ⊗ c.obj b)
    (hm : ∀ {a a' b b' : C} (x : a ⟶ a') (y : b ⟶ b'),
      c.map (x ⊗ₘ y) ≫ m a' b' = m a b ≫ (c.map x ⊗ₘ c.map y))
    {X₁ Y₁ X₂ Y₂ W : C} (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂) (μ : Y₁ ⊗ Y₂ ⟶ W)
    {X₁' Y₁' X₂' Y₂' W' : C'} (a₁' : X₁' ⟶ Y₁') (a₂' : X₂' ⟶ Y₂') (μ' : Y₁' ⊗ Y₂' ⟶ W')
    (s₁ : c.obj X₁ ⟶ X₁') (t₁ : c.obj Y₁ ⟶ Y₁') (s₂ : c.obj X₂ ⟶ X₂') (t₂ : c.obj Y₂ ⟶ Y₂')
    (w : c.obj W ⟶ W') (h₁ : c.map a₁ ≫ t₁ = s₁ ≫ a₁') (h₂ : c.map a₂ ≫ t₂ = s₂ ≫ a₂')
    (hμ : c.map μ ≫ w = m Y₁ Y₂ ≫ (t₁ ⊗ₘ t₂) ≫ μ') :
    c.map ((a₁ ⊗ₘ a₂) ≫ μ) ≫ w = m X₁ X₂ ≫ (s₁ ⊗ₘ s₂) ≫ (a₁' ⊗ₘ a₂') ≫ μ' := by
  rw [c.map_comp, Category.assoc, hμ, reassoc_of% (hm a₁ a₂), tensorHom_comp_tensorHom_assoc,
    h₁, h₂, ← tensorHom_comp_tensorHom_assoc]


/-- Postcomposing a square `x ≫ w₀ = m ≫ (t₁ ⊗ t₂) ≫ μ₀` with a naturality square
`(u₁ ⊗ u₂) ≫ μ' = μ₀ ≫ v` of lax tensor maps. -/
lemma comp_tensorHom_comp_eq_of_comp_eq {X₀ Y₀ W₀ W' A₁ A₂ Y₁ Y₂ Z₁ Z₂ : C'} (x : X₀ ⟶ Y₀)
    (w₀ : Y₀ ⟶ W₀) (m : X₀ ⟶ A₁ ⊗ A₂) (t₁ : A₁ ⟶ Y₁) (t₂ : A₂ ⟶ Y₂) (μ₀ : Y₁ ⊗ Y₂ ⟶ W₀)
    (u₁ : Y₁ ⟶ Z₁) (u₂ : Y₂ ⟶ Z₂) (μ' : Z₁ ⊗ Z₂ ⟶ W') (v : W₀ ⟶ W')
    (h : x ≫ w₀ = m ≫ (t₁ ⊗ₘ t₂) ≫ μ₀) (hn : (u₁ ⊗ₘ u₂) ≫ μ' = μ₀ ≫ v) :
    x ≫ w₀ ≫ v = m ≫ ((t₁ ≫ u₁) ⊗ₘ (t₂ ≫ u₂)) ≫ μ' := by
  rw [reassoc_of% h, ← tensorHom_comp_tensorHom, Category.assoc, hn]
end Tensor
section Bifunctor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']

/-- A natural transformation `F (- ⊗ -) ⟶ F - ⊗ F -` of bifunctors is natural for the tensor
product of morphisms. -/
lemma Functor.map_tensorHom_comp_app_app {F : C ⥤ D}
    (e : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    {K K' M M' : C} (x : K ⟶ K') (y : M ⟶ M') :
    F.map (x ⊗ₘ y) ≫ (e.app K').app M' = (e.app K).app M ≫ (F.map x ⊗ₘ F.map y) := by
  have h₁ := congr_app (e.naturality x) M
  have h₂ := (e.app K').naturality y
  dsimp at h₁ h₂
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁, tensorHom_def]

/-- `CategoryTheory.Adjunction.ComparisonCompatible` for the tensor products, pointwise, in
terms of tensor products of morphisms. -/
lemma Adjunction.ComparisonCompatible.tensorHom {F : D ⥤ C} {F' : D' ⥤ C'} {N_D : D ⥤ D'}
    {N_C : C ⥤ C'} {α : N_D ⋙ F' ≅ F ⋙ N_C}
    {φ : (Functor.postcompose₂.obj F).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C)}
    {φ' : (Functor.postcompose₂.obj F').obj (curriedTensor D') ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj (curriedTensor C')}
    {m_C : (Functor.postcompose₂.obj N_C).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ C').obj N_C).obj N_C).obj (curriedTensor C')}
    {m_D : (Functor.postcompose₂.obj N_D).obj (curriedTensor D) ≅
      (((Functor.whiskeringLeft₂ D').obj N_D).obj N_D).obj (curriedTensor D')}
    (H : Adjunction.ComparisonCompatible α φ φ' m_C m_D) (a b : D) :
    N_C.map ((φ.app a).app b) ≫ (m_C.hom.app (F.obj a)).app (F.obj b) =
      α.inv.app (a ⊗ b) ≫ F'.map ((m_D.hom.app a).app b) ≫
        (φ'.app (N_D.obj a)).app (N_D.obj b) ≫ (α.hom.app a ⊗ₘ α.hom.app b) := by
  rw [tensorHom_def]
  exact H a b

end Bifunctor

end CategoryTheory
