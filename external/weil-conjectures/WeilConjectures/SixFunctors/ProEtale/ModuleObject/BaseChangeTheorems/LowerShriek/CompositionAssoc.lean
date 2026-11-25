/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.CompositionCoherence
public import WeilConjectures.Compactification.TriangleAssoc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeMate

/-!

# Associativity of the composition isomorphisms of the lower shriek

For composable morphisms `f : W ⟶ X`, `g : X ⟶ Y`, `h : Y ⟶ Z` of separated `k`-schemes of finite
type, the two identifications of `R(f ≫ g ≫ h)_!` with `Rf_! ⋙ Rg_! ⋙ Rh_!` on bounded
constructible `ℚ̄_ℓ`-sheaves built from the composition isomorphisms agree
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_assoc'`, blueprint
`prop-functor-package`, clause (3)).

The proof computes the four composition isomorphisms through the four triangles of
compactifications of a staircase of cartesian squares
(`Compactification.Triangle.assocLeft`, `Compactification.Triangle.assocRight`), by
`boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle`, and concludes by the
associativity of the composition isomorphisms of an exchange formalism
(`CategoryTheory.ExchangeFormalism.compIso_assoc`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

/-- An algebraic identity used to reduce the associativity of composition isomorphisms computed
through comparisons `a`, `a'`, `b`, `c` to the associativity `hτ` of the composition
isomorphisms `τ₁`, `τ₂`, `τ₃`, `τ₄`. -/
lemma CategoryTheory.Iso.hcomp_app_comp_map_eq_of_assoc {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜]
    [Category* ℬ] [Category* 𝒞] [Category* 𝒟] (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) (H : 𝒞 ⥤ 𝒟)
    {L L' L₃ L₃' : 𝒜 ⥤ 𝒟} {L₁ L₁' : 𝒜 ⥤ 𝒞} {L₂ L₂' : ℬ ⥤ 𝒟} (a : L ≅ L₃) (a' : L' ≅ L₃')
    (τ₃ : L₁ ⋙ H ≅ L₃) (τ₁ : F ⋙ G ≅ L₁) (τ₄ : F ⋙ L₂ ≅ L₃') (τ₂ : G ⋙ H ≅ L₂) (b : L₁ ≅ L₁')
    (c : L₂ ≅ L₂') (K : 𝒜) (e : L.obj K = L'.obj K)
    (hτ : a.hom.app K ≫ τ₃.inv.app K ≫ H.map (τ₁.inv.app K) =
      eqToHom e ≫ a'.hom.app K ≫ τ₄.inv.app K ≫ τ₂.inv.app (F.obj K)) :
    (a.hom ≫ τ₃.inv ≫ NatTrans.hcomp b.hom (𝟙 H)).app K ≫
        H.map ((b.symm.hom ≫ τ₁.inv ≫ NatTrans.hcomp (𝟙 F) (𝟙 G)).app K) =
      eqToHom e ≫ (a'.hom ≫ τ₄.inv ≫ NatTrans.hcomp (𝟙 F) c.hom).app K ≫
        (c.symm.hom ≫ τ₂.inv ≫ NatTrans.hcomp (𝟙 G) (𝟙 H)).app (F.obj K) := by
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, NatTrans.id_app, Functor.map_id,
    Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc, Iso.symm_hom,
    Functor.comp_obj]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc]
  exact hτ

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

section Composition

variable {W X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsSeparated W.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

section Staircase

open Compactification.Triangle

variable {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z} {cf : Compactification f.left}
  {cg : Compactification g.left} {ch : Compactification h.left}
  {dfg : Compactification (cf.overG ≫ cg.overI).left}
  {dgh : Compactification (cg.overG ≫ ch.overI).left}
  {dV : Compactification (dfg.overG ≫ dgh.overI).left}
  (hfg : IsPullback cf.overG dfg.overI cg.overI dfg.overG)
  (hgh : IsPullback cg.overG dgh.overI ch.overI dgh.overG)
  (hV : IsPullback dfg.overG dV.overI dgh.overI dV.overG)

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsSeparated W.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
/-- The middle square `b ≫ c = e ≫ u` of the staircase of compactifications is cartesian. -/
lemma isPullback_overP_overQ_assoc :
    IsPullback (overP (triangleOfCompactifications cf cg dfg hfg))
      (overQ (Compactification.Triangle.assocLeft hgh hV))
      (overQ (triangleOfCompactifications cg ch dgh hgh))
      (overP (Compactification.Triangle.assocRight hfg hV)) :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (hV.map (Over.forget _)).w)
    (hV.map (Over.forget _))

-- the instance of `compIso_assoc` unifies the four triangles of the staircase
/-- **Associativity of the composition isomorphisms of the staircase of triangles of
compactifications**, an instance of `CategoryTheory.ExchangeFormalism.compIso_assoc`. -/
theorem compIso_triangleShriekTriangle_assoc (K : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications cf cg dfg hfg)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications cf cg dfg hfg)
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications cg ch dgh hgh)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications cg ch dgh hgh)
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (assocLeft hgh hV)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (assocLeft hgh hV)
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (assocRight hfg hV)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (assocRight hfg hV)
    ((𝔽).compIso (triangleShriekTriangle (assocLeft hgh hV))).inv.app K ≫
        ((𝔽).shriek (triangleShriekTriangle (assocLeft hgh hV)).i₂
          (triangleShriekTriangle (assocLeft hgh hV)).p₂).map
          (((𝔽).compIso (triangleShriekTriangle
            (triangleOfCompactifications cf cg dfg hfg))).inv.app K) =
      ((𝔽).compIso (triangleShriekTriangle (assocRight hfg hV))).inv.app K ≫
        ((𝔽).compIso (triangleShriekTriangle
          (triangleOfCompactifications cg ch dgh hgh))).inv.app
          (((𝔽).shriek (triangleShriekTriangle (assocRight hfg hV)).i₁
            (triangleShriekTriangle (assocRight hfg hV)).p₁).obj K) := by
  have := isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
    (isPullback_overP_overQ_assoc hfg hgh hV)
  have := isIso_exchange_boundedConstructibleExchangeFormalism ℓ
    (isPullback_overP_overQ_assoc hfg hgh hV)
  have := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications cf cg dfg hfg)
  have := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications cf cg dfg hfg)
  have := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications cg ch dgh hgh)
  have := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications cg ch dgh hgh)
  have := isIso_baseChange_triangleShriekTriangle ℓ (assocLeft hgh hV)
  have := isIso_exchange_triangleShriekTriangle ℓ (assocLeft hgh hV)
  have := isIso_baseChange_triangleShriekTriangle ℓ (assocRight hfg hV)
  have := isIso_exchange_triangleShriekTriangle ℓ (assocRight hfg hV)
  have key := (𝔽).compIso_assoc
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).i₁
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).p₁
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).i₂
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).p₂
    (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)).i₂
    (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)).p₂
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).q
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).r
    (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)).q
    (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)).r
    (triangleShriekTriangle (assocLeft hgh hV)).q
    (triangleShriekTriangle (assocRight hfg hV)).r
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).i
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).p
    (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)).i
    (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)).p
    (triangleShriekTriangle (assocRight hfg hV)).q
    (triangleShriekTriangle (assocLeft hgh hV)).r
    (triangleShriekTriangle (assocLeft hgh hV)).i
    (triangleShriekTriangle (assocLeft hgh hV)).p
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).i_q
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).r_p
    (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)).i_q
    (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)).r_p
    (triangleShriekTriangle (assocLeft hgh hV)).i_q
    (triangleShriekTriangle (assocRight hfg hV)).i_q
    (triangleShriekTriangle (assocLeft hgh hV)).r_p
    (triangleShriekTriangle (assocRight hfg hV)).r_p
    (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)).w
    (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)).w
    (SepFinType.homMk_comp_homMk (isPullback_overP_overQ_assoc hfg hgh hV).w)
    (triangleShriekTriangle (assocLeft hgh hV)).w
    (triangleShriekTriangle (assocRight hfg hV)).w
    (ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl))
    (ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl)) K
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
  · congr 1

-- The statement unfolds the staircase triangles of three compactifications.
/-- **Associativity of the composition isomorphisms computed through the staircase**: the
associativity equation of the composition isomorphisms of the lower shriek, with each
composition isomorphism expressed through its triangle of the staircase of compactifications
(`boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle`), for arbitrary
compactifications `c₁₂`, `c₂₃`, `c₁₂₃` of `f ≫ g`, `g ≫ h`, `f ≫ g ≫ h`. -/
theorem compIso_triangleShriekTriangle_assoc_comparison
    (c₁₂ : Compactification (f ≫ g).left) (c₂₃ : Compactification (g ≫ h).left)
    (c₁₂₃ : Compactification ((f ≫ g) ≫ h).left) (c₁₂₃' : Compactification (f ≫ g ≫ h).left)
    (hc : c₁₂₃' = c₁₂₃) (K : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : (boundedConstructibleLowerShriekOfCompactification ℓ c₁₂₃).obj K =
      (boundedConstructibleLowerShriekOfCompactification ℓ c₁₂₃').obj K) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications cf cg dfg hfg)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications cf cg dfg hfg)
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications cg ch dgh hgh)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications cg ch dgh hgh)
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (assocLeft hgh hV)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (assocLeft hgh hV)
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (assocRight hfg hV)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (assocRight hfg hV)
    ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁₂₃
          (overCfg (assocLeft hgh hV))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (assocLeft hgh hV))).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (assocLeft hgh hV).cf c₁₂).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (assocLeft hgh hV).cg ch).hom).app K ≫
      (boundedConstructibleLowerShriekOfCompactification ℓ ch).map
        (((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁₂
          (overCfg (triangleOfCompactifications cf cg dfg hfg))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg))).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (triangleOfCompactifications cf cg dfg hfg).cf cf).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (triangleOfCompactifications cf cg dfg hfg).cg cg).hom).app K) =
    eqToHom e ≫
      ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁₂₃'
          (overCfg (assocRight hfg hV))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (assocRight hfg hV))).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (assocRight hfg hV).cf cf).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (assocRight hfg hV).cg c₂₃).hom).app K ≫
      ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₂₃
          (overCfg (triangleOfCompactifications cg ch dgh hgh))).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh))).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (triangleOfCompactifications cg ch dgh hgh).cf cg).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            (triangleOfCompactifications cg ch dgh hgh).cg ch).hom).app
        ((boundedConstructibleLowerShriekOfCompactification ℓ cf).obj K) := by
  have r₁ : boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (assocLeft hgh hV).cg ch = Iso.refl _ :=
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl ℓ _
  have r₂ : boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (triangleOfCompactifications cf cg dfg hfg).cf cf = Iso.refl _ :=
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl ℓ _
  have r₃ : boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (triangleOfCompactifications cf cg dfg hfg).cg cg = Iso.refl _ :=
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl ℓ _
  have s₁ : boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁₂
      (overCfg (triangleOfCompactifications cf cg dfg hfg)) =
        (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (assocLeft hgh hV).cf c₁₂).symm :=
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ _ _).symm
  have s₂ : boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₂₃
      (overCfg (triangleOfCompactifications cg ch dgh hgh)) =
        (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (assocRight hfg hV).cg c₂₃).symm :=
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_symm ℓ _ _).symm
  simp only [r₁, r₂, r₃, s₁, s₂]
  have := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications cf cg dfg hfg)
  have := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications cf cg dfg hfg)
  have := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications cg ch dgh hgh)
  have := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications cg ch dgh hgh)
  have := isIso_baseChange_triangleShriekTriangle ℓ (assocLeft hgh hV)
  have := isIso_exchange_triangleShriekTriangle ℓ (assocLeft hgh hV)
  have := isIso_baseChange_triangleShriekTriangle ℓ (assocRight hfg hV)
  have := isIso_exchange_triangleShriekTriangle ℓ (assocRight hfg hV)
  refine Iso.hcomp_app_comp_map_eq_of_assoc (boundedConstructibleLowerShriekOfCompactification ℓ cf)
    (boundedConstructibleLowerShriekOfCompactification ℓ cg)
    (boundedConstructibleLowerShriekOfCompactification ℓ ch)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁₂₃
      (overCfg (assocLeft hgh hV)))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c₁₂₃'
      (overCfg (assocRight hfg hV)))
    ((𝔽).compIso (triangleShriekTriangle (assocLeft hgh hV)))
    ((𝔽).compIso (triangleShriekTriangle (triangleOfCompactifications cf cg dfg hfg)))
    ((𝔽).compIso (triangleShriekTriangle (assocRight hfg hV)))
    ((𝔽).compIso (triangleShriekTriangle (triangleOfCompactifications cg ch dgh hgh)))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (assocLeft hgh hV).cf c₁₂)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (assocRight hfg hV).cg c₂₃) K e ?_
  refine (congrArg (_ ≫ ·) (compIso_triangleShriekTriangle_assoc ℓ hfg hgh hV K)).trans ?_
  subst hc
  rw [eqToHom_refl _ e, Category.id_comp]
  congr 1

end Staircase

/-- **Associativity of the composition isomorphisms of the lower shriek** (blueprint
`prop-functor-package`, clause (3)): the two identifications of `R(f ≫ g ≫ h)_!` with
`Rf_! ⋙ Rg_! ⋙ Rh_!` agree. -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_assoc' (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (K : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (f ≫ g) h).hom.app K ≫
        (boundedConstructibleLowerShriek ℓ h).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app K) =
      eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f (g ≫ h)).hom.app K ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).hom.app
          ((boundedConstructibleLowerShriek ℓ f).obj K) := by
  obtain ⟨dfg, hfg⟩ := Compactification.exists_isPullback_overG_overI
    (compactificationOverField f) (compactificationOverField g)
  obtain ⟨dgh, hgh⟩ := Compactification.exists_isPullback_overG_overI
    (compactificationOverField g) (compactificationOverField h)
  obtain ⟨dV, hV⟩ := Compactification.exists_isPullback_overG_overI dfg dgh
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ (f ≫ g) h
      (Compactification.Triangle.assocLeft hgh hV),
    boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ f g
      (triangleOfCompactifications _ _ dfg hfg),
    boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ f (g ≫ h)
      (Compactification.Triangle.assocRight hfg hV),
    boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle ℓ g h
      (triangleOfCompactifications _ _ dgh hgh)]
  exact compIso_triangleShriekTriangle_assoc_comparison ℓ hfg hgh hV
    (compactificationOverField (f ≫ g)) (compactificationOverField (g ≫ h))
    (compactificationOverField ((f ≫ g) ≫ h)) (compactificationOverField (f ≫ g ≫ h)) rfl K _

end Composition

end AlgebraicGeometry.ProEtale.CondensedRing
