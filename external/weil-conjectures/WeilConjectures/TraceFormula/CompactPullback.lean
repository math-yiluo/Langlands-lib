/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.Frobenius

/-!

# The pullback on compactly supported cohomology along a proper morphism

Let `h : Y ⟶ X` be a proper morphism of separated `k`-schemes of finite type. The *pullback*
along `h` on compactly supported cohomology is the composite
```
h^♯ : RΓ_c(X, K) = Ra_{X!} K ⟶ Ra_{X!} Rh_* Lh^* K ≅ Ra_{X!} Rh_! Lh^* K ≅ R(h ≫ a_X)_! Lh^* K
        = Ra_{Y!} Lh^* K = RΓ_c(Y, Lh^* K)
```
of the unit of `Lh^* ⊣ Rh_*`, the identification `Rh_! ≅ Rh_*` of the proper `h` and the
composition isomorphism of the lower shriek (`ProEtale.CondensedRing.compactPullback`). It is
the first half of the global operator of a graph correspondence (blueprint
`definition-frobenius-correspondences-their-operators--5`): for `c = (𝟙 X, h)` and `v : Lh^* K ⟶ K`
the global operator is `RΓ_c(X, v) ∘ h^♯`.

The pullbacks are compatible with composition, `(g ≫ h)^♯ = Lg^*… ∘ g^♯ ∘ h^♯`
(`ProEtale.CondensedRing.compactPullback_comp_app`), and for the identity of `X` the
compact-support base change `Ex_!` along the trivial square is the identity up to the identity
isomorphisms of the pullbacks
(`ProEtale.CondensedRing.boundedConstructibleUpperStarId_inv_app_comp_baseChange_app`).

## Frobenius coefficient morphisms

For an endomorphism `Φ` of `X` and an arbitrary morphism `ψ : LΦ^* K ⟶ K` (a *Frobenius
coefficient morphism*, blueprint `definition-frobenius-correspondences-their-operators`) the
iterates `ψ_m : LΦ_m^* K ⟶ K` are defined as for Weil structures
(`ProEtale.CondensedRing.frobeniusCoefficientIterate`), and for `Φ` proper the global operator
of degree `m` is `F_{c,m}(ψ) = RΓ_c(X, ψ_m) ∘ Φ_m^♯`
(`ProEtale.CondensedRing.frobeniusCompactOperator`). It is the `m`-th power of the operator of
degree one (`ProEtale.CondensedRing.frobeniusCompactOperator_eq_pow`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### An abstract identity for mates -/

section Abstract

variable {C E : Type*} [Category C] [Category E] {G : C ⥤ E} {L₁ R₁ : C ⥤ C} {L₂ R₂ : E ⥤ E}

/-- Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions of endofunctors with identifications
`L_i ≅ 𝟭` and `R_i ≅ 𝟭` compatible with the units, and let `β : R₁ ⋙ G ⟶ G ⋙ R₂` be the
identity under these identifications. Then the mate `G ⋙ L₂ ⟶ L₁ ⋙ G` of `β` is the identity
under these identifications. -/
lemma mateEquiv_symm_app_of_iso_aux (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (eL₁ : L₁ ≅ 𝟭 C)
    (eR₁ : R₁ ≅ 𝟭 C) (eL₂ : L₂ ≅ 𝟭 E) (eR₂ : R₂ ≅ 𝟭 E)
    (h₁ : ∀ M, adj₁.unit.app M ≫ eR₁.hom.app (L₁.obj M) = eL₁.inv.app M)
    (h₂ : ∀ N, adj₂.unit.app N ≫ eR₂.hom.app (L₂.obj N) = eL₂.inv.app N)
    (β : TwoSquare R₁ G G R₂)
    (hβ : ∀ N, β.app N ≫ eR₂.hom.app (G.obj N) = G.map (eR₁.hom.app N)) (M : C) :
    eL₂.inv.app (G.obj M) ≫ ((mateEquiv adj₁ adj₂).symm β).app M =
      G.map (eL₁.inv.app M) := by
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom]
  apply (adj₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine (unit_mateEquiv_symm adj₁ adj₂ β M).symm.trans ?_
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [← cancel_mono (eR₂.hom.app (G.obj (L₁.obj M))), Category.assoc, hβ, ← G.map_comp, h₁,
    Category.assoc, eR₂.hom.naturality, Functor.id_map, ← Category.assoc, h₂,
    Iso.inv_hom_id_app_assoc]

end Abstract

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The pullback on compactly supported cohomology -/

section CompactPullback

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The composition isomorphism `Rh_! ⋙ Ra_{X!} ≅ R(h ≫ a_X)_! = Ra_{Y!}` of the lower shriek
along `h : Y ⟶ X` and the structure morphism of `X`. -/
noncomputable def boundedConstructibleLowerShriekCompToPoint (h : Y ⟶ X) :
    boundedConstructibleLowerShriek ℓ h ⋙
        boundedConstructibleLowerShriek ℓ (toPoint X) ≅
      boundedConstructibleLowerShriek ℓ (toPoint Y) :=
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h (toPoint X)).symm ≪≫
    eqToIso (by rw [comp_toPoint])

lemma boundedConstructibleLowerShriekCompToPoint_hom_app (h : Y ⟶ X)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekCompToPoint ℓ h).hom.app M =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h (toPoint X)).inv.app M ≫
        eqToHom (by rw [comp_toPoint]) := by
  simp only [boundedConstructibleLowerShriekCompToPoint, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app]

lemma boundedConstructibleLowerShriekCompToPoint_inv_app (h : Y ⟶ X)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekCompToPoint ℓ h).inv.app M =
      eqToHom (by rw [comp_toPoint]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h (toPoint X)).hom.app M := by
  simp only [boundedConstructibleLowerShriekCompToPoint, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.inv, eqToHom_app]


/-- The composition isomorphisms of the lower shriek along equal morphisms agree up to the
casts. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_congr (g : Z ⟶ Y) {b b' : Y ⟶ X}
    (e : b = b') (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).hom.app M =
      eqToHom (by rw [e]) ≫ (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b').hom.app M ≫
        eqToHom (by rw [e]) := by
  subst e
  simp

/-- Associativity of the composition isomorphisms `Rh_! ⋙ Ra_{X!} ≅ Ra_{Y!}`. -/
lemma boundedConstructibleLowerShriekCompToPoint_assoc (g : Z ⟶ Y) (h : Y ⟶ X)
    (M : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekCompToPoint ℓ (g ≫ h)).inv.app M ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).hom.app M) =
      (boundedConstructibleLowerShriekCompToPoint ℓ g).inv.app M ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ h).inv.app
          ((boundedConstructibleLowerShriek ℓ g).obj M) := by
  rw [boundedConstructibleLowerShriekCompToPoint_inv_app,
    boundedConstructibleLowerShriekCompToPoint_inv_app,
    boundedConstructibleLowerShriekCompToPoint_inv_app, Category.assoc,
    boundedConstructibleLowerShriekComp_padicAlgCl_assoc,
    boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_congr ℓ g (comp_toPoint h) M]
  simp only [Category.assoc, eqToHom_trans_assoc]

/-- The *pullback on compactly supported cohomology* `h^♯ : RΓ_c(X, -) ⟶ RΓ_c(Y, Lh^* -)` along
a proper morphism `h : Y ⟶ X` (blueprint `definition-frobenius-correspondences-their-operators--5`):
the composite
```
Ra_{X!} K ⟶ Ra_{X!} Rh_* Lh^* K ≅ Ra_{X!} Rh_! Lh^* K ≅ R(h ≫ a_X)_! Lh^* K = Ra_{Y!} Lh^* K
```
of the unit of `Lh^* ⊣ Rh_*`, the identification `Rh_! ≅ Rh_*` and the composition isomorphism
of the lower shriek. -/
noncomputable def compactPullback (h : Y ⟶ X) [IsProper h.left] :
    boundedConstructibleLowerShriek ℓ (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h ⋙
        boundedConstructibleLowerShriek ℓ (toPoint Y) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ h).unit
      _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerRight
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv _) ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekCompToPoint ℓ h).hom

lemma compactPullback_app (h : Y ⟶ X) [IsProper h.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ h).app K =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            h).unit.app K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv.app _) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ h).hom.app _ := by
  simp only [compactPullback, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp]

/-- The pullback along `h` is natural in the coefficient complex. -/
@[reassoc]
lemma compactPullback_naturality (h : Y ⟶ X) [IsProper h.left]
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a : K ⟶ K') :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map a ≫
        (compactPullback ℓ h).app K' =
      (compactPullback ℓ h).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).map a) :=
  (compactPullback ℓ h).naturality a

/-- The pullbacks along equal morphisms agree up to the cast. -/
lemma compactPullback_app_congr {h h' : Y ⟶ X} (e : h = h') [IsProper h.left]
    [IsProper h'.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ h).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          (eqToHom (by rw [e])) =
      (compactPullback ℓ h').app K := by
  subst e
  simp

/-- The composition law of `compactPullback`, for an abstract family of functors. -/
lemma compactPullback_comp_aux {DX DY DZ S : Type*} [Category DX] [Category DY] [Category DZ]
    [Category S] {Lh : DX ⥤ DY} {Lg : DY ⥤ DZ} {Lgh : DX ⥤ DZ} {Rh : DY ⥤ DX} {Rg : DZ ⥤ DY}
    {Rgh : DZ ⥤ DX} {Sh : DY ⥤ DX} {Sg : DZ ⥤ DY} {Sgh : DZ ⥤ DX} {AX : DX ⥤ S} {AY : DY ⥤ S}
    {AZ : DZ ⥤ S} (adjh : Lh ⊣ Rh) (adjg : Lg ⊣ Rg) (adjgh : Lgh ⊣ Rgh) (ih : Sh ≅ Rh)
    (ig : Sg ≅ Rg) (igh : Sgh ≅ Rgh) (uc : Lgh ≅ Lh ⋙ Lg) (lc : Rg ⋙ Rh ≅ Rgh)
    (sc : Sgh ≅ Sg ⋙ Sh) (ch : Sh ⋙ AX ≅ AY) (cg : Sg ⋙ AY ≅ AZ) (cgh : Sgh ⋙ AX ≅ AZ)
    (hU : ∀ K, adjgh.unit.app K ≫ lc.inv.app (Lgh.obj K) =
      adjh.unit.app K ≫ Rh.map (adjg.unit.app (Lh.obj K)) ≫ Rh.map (Rg.map (uc.inv.app K)))
    (hL : ∀ P, sc.hom.app P ≫ ih.hom.app (Sg.obj P) ≫ Rh.map (ig.hom.app P) =
      igh.hom.app P ≫ lc.inv.app P)
    (hA : ∀ P, cgh.inv.app P ≫ AX.map (sc.hom.app P) = cg.inv.app P ≫ ch.inv.app (Sg.obj P))
    (K : DX) :
    AX.map (adjgh.unit.app K) ≫ AX.map (igh.inv.app _) ≫ cgh.hom.app _ =
      (AX.map (adjh.unit.app K) ≫ AX.map (ih.inv.app _) ≫ ch.hom.app _) ≫
        (AY.map (adjg.unit.app (Lh.obj K)) ≫ AY.map (ig.inv.app _) ≫ cg.hom.app _) ≫
        AZ.map (uc.inv.app K) := by
  have hA' (P : DZ) : ch.hom.app (Sg.obj P) ≫ cg.hom.app P =
      AX.map (sc.inv.app P) ≫ cgh.hom.app P := by
    have h₁ : AX.map (sc.hom.app P) = cgh.hom.app P ≫ cg.inv.app P ≫ ch.inv.app (Sg.obj P) := by
      rw [← hA, Iso.hom_inv_id_app_assoc]
    refine (cancel_epi (AX.map (sc.hom.app P))).1 ?_
    rw [← AX.map_comp_assoc, Iso.hom_inv_id_app, AX.map_id, Category.id_comp, h₁]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hL' (P : DZ) : Rh.map (ig.inv.app P) ≫ ih.inv.app (Sg.obj P) ≫ sc.inv.app P =
      lc.hom.app P ≫ igh.inv.app P := by
    refine (cancel_epi (lc.inv.app P)).1 ?_
    refine (cancel_epi (igh.hom.app P)).1 ?_
    rw [Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app, ← reassoc_of% (hL P)]
    simp only [← Rh.map_comp_assoc, Iso.hom_inv_id_app, Rh.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc]
  have hU' : adjgh.unit.app K = adjh.unit.app K ≫ Rh.map (adjg.unit.app (Lh.obj K)) ≫
      Rh.map (Rg.map (uc.inv.app K)) ≫ lc.hom.app (Lgh.obj K) := by
    rw [← reassoc_of% (hU K), Iso.inv_hom_id_app, Category.comp_id]
  have key : adjgh.unit.app K ≫ igh.inv.app (Lgh.obj K) =
      adjh.unit.app K ≫ ih.inv.app (Lh.obj K) ≫ Sh.map (adjg.unit.app (Lh.obj K)) ≫
        Sh.map (ig.inv.app _) ≫ sc.inv.app _ ≫ Sgh.map (uc.inv.app K) := by
    rw [hU', ← ih.inv.naturality_assoc, ← ih.inv.naturality_assoc, reassoc_of% (hL' _),
      ← igh.inv.naturality, ← lc.hom.naturality_assoc]
    simp only [Functor.comp_map, Category.assoc]
  simp only [Category.assoc]
  rw [← ch.hom.naturality_assoc, ← ch.hom.naturality_assoc, reassoc_of% (hA' _),
    ← cgh.hom.naturality, ← AX.map_comp_assoc, key]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

-- matching the unit of the composite adjunction unfolds the restricted `ℚ̲̄_ℓ`-functors
/-- **Compatibility of the pullbacks with composition** (blueprint
`definition-frobenius-correspondences-their-operators--5`): `(g ≫ h)^♯` is `h^♯` followed by `g^♯`
and the composition isomorphism `Lg^* Lh^* ≅ L(g ≫ h)^*`. -/
lemma compactPullback_comp_app (g : Z ⟶ Y) (h : Y ⟶ X) [IsProper g.left] [IsProper h.left]
    [IsProper (g ≫ h).left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ (g ≫ h)).app K =
      (compactPullback ℓ h).app K ≫
        (compactPullback ℓ g).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g h).inv.app
            K) := by
  rw [compactPullback_app, compactPullback_app, compactPullback_app]
  refine compactPullback_comp_aux
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ h)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (g ≫ h))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (g ≫ h))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g h)
    (boundedConstructibleLowerStarComp ℓ g h)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h)
    (boundedConstructibleLowerShriekCompToPoint ℓ h)
    (boundedConstructibleLowerShriekCompToPoint ℓ g)
    (boundedConstructibleLowerShriekCompToPoint ℓ (g ≫ h))
    (fun K ↦ ?_) (fun P ↦ ?_) (fun P ↦ ?_) K
  · have hu := unit_conjugateEquiv
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (g ≫ h))
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
        h).comp
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ g))
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g h).inv K
    rw [Adjunction.comp_unit_app, Category.assoc] at hu
    exact hu
  · exact boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ g h P
  · exact boundedConstructibleLowerShriekCompToPoint_assoc ℓ g h P

end CompactPullback

/-! ### The identity -/

section Identity

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

variable (X) in
/-- The unit of `L(𝟙 X)^* ⊣ R(𝟙 X)_!` is the identity, up to the identity isomorphisms
`L(𝟙 X)^* ≅ 𝟭` and `R(𝟙 X)_! ≅ R(𝟙 X)_* ≅ 𝟭`. -/
lemma boundedConstructibleUpperStarLowerShriekAdjunction_id_unit_app
    [IsProper (𝟙 X : X ⟶ X).left] (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (𝟙 X)).unit.app M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X) ≪≫
          boundedConstructibleLowerStarId ℓ X).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)).obj M) =
      (boundedConstructibleUpperStarId _ ℓ X).inv.app M := by
  have h := unit_conjugateEquiv
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X))
    Adjunction.id (boundedConstructibleUpperStarId _ ℓ X).inv M
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [boundedConstructibleLowerStarId, conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  exact h.trans (Category.id_comp _)

/-- The composition isomorphisms `R(𝟙 ≫ a)_! ≅ R(𝟙)_! ⋙ Ra_!` and `R(a ≫ 𝟙)_! ≅ Ra_! ⋙ R(𝟙)_!`
of the trivial square `𝟙 X ≫ a_X = a_X ≫ 𝟙 s` are compatible with the identity isomorphisms
`R(𝟙)_! ≅ 𝟭`. -/
lemma boundedConstructibleLowerShriekSquareIso_toPoint_hom_app
    [IsProper (𝟙 X : X ⟶ X).left] [IsProper (𝟙 (point k) : point k ⟶ point k).left]
    (w : 𝟙 X ≫ toPoint X = toPoint X ≫ 𝟙 (point k))
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app N ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 (point k)) ≪≫
          boundedConstructibleLowerStarId ℓ (point k)).hom.app
          ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj
            N) =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X) ≪≫
          boundedConstructibleLowerStarId ℓ X).hom.app N) := by
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 X) (toPoint X)).hom.app
    N)]
  simp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_id_right,
    boundedConstructibleLowerShriekComp_padicAlgCl_id_left, eqToHom_trans]

/-- **Compact-support base change along the identity.** For the trivial cartesian square
`𝟙 X ≫ a_X = a_X ≫ 𝟙 s`, the base change `Ex_! : Ra_{X!} ⋙ L(𝟙 s)^* ⟶ L(𝟙 X)^* ⋙ Ra_{X!}` is
the identity up to the identity isomorphisms of the pullbacks. -/
lemma boundedConstructibleUpperStarId_inv_app_comp_baseChange_app
    (sq : IsPullback (𝟙 X) (toPoint X) (toPoint X) (𝟙 (point k)))
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarId _ ℓ (point k)).inv.app
        ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app M =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleUpperStarId _ ℓ X).inv.app M) := by
  have : IsProper (𝟙 X : X ⟶ X).left := inferInstanceAs (IsProper (𝟙 X.left))
  have : IsProper (𝟙 (point k) : point k ⟶ point k).left :=
    inferInstanceAs (IsProper (𝟙 (Spec (.of k))))
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv]
  exact mateEquiv_symm_app_of_iso_aux _ _ _ _ _ _
    (boundedConstructibleUpperStarLowerShriekAdjunction_id_unit_app ℓ X)
    (boundedConstructibleUpperStarLowerShriekAdjunction_id_unit_app ℓ (point k)) _
    (boundedConstructibleLowerShriekSquareIso_toPoint_hom_app ℓ sq.w) M


variable (X) in
/-- The pullback along the identity is the identity isomorphism `𝟭 ≅ L(𝟙 X)^*`. -/
lemma compactPullback_id_app [IsProper (𝟙 X : X ⟶ X).left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ (𝟙 X)).app K =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleUpperStarId _ ℓ X).inv.app K) := by
  have hl := boundedConstructibleLowerShriekComp_padicAlgCl_id_left ℓ (toPoint X)
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X)).obj K)
  have hu := boundedConstructibleUpperStarLowerShriekAdjunction_id_unit_app ℓ X K
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_hom,
    Iso.symm_hom, Category.assoc] at hu
  rw [compactPullback_app, boundedConstructibleLowerShriekCompToPoint_hom_app, ← hu]
  simp only [Functor.map_comp]
  congr 2
  rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 X) (toPoint X)).hom.app
    _), Iso.hom_inv_id_app_assoc, ← Functor.map_comp, hl]

end Identity

/-! ### Compatibility with compact-support base change -/

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The composition isomorphisms `Rb_! ⋙ Ra_Y ≅ Ra_{X'}` along equal morphisms agree up to the
cast. -/
lemma boundedConstructibleLowerShriekCompToPoint_hom_app_congr {b b' : X ⟶ Y} (e : b = b')
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        (eqToHom (congrArg (fun b ↦
          (boundedConstructibleLowerShriek ℓ b).obj M) e)) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ b').hom.app M =
      (boundedConstructibleLowerShriekCompToPoint ℓ b).hom.app M := by
  subst e
  simp

/-- The composition isomorphisms `Rh_! ⋙ Ra ≅ Ra` are compatible with the composition
isomorphism `Rg'_! ⋙ Rf_! ≅ Rf'_! ⋙ Rg_!` of a commutative square `g' ≫ f = f' ≫ g`. -/
lemma boundedConstructibleLowerShriekSquareIso_compToPoint (w : g' ≫ f = f' ≫ g)
    (M : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app M) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ g).hom.app
        ((boundedConstructibleLowerShriek ℓ f').obj M) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ f').hom.app M =
    (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app
        ((boundedConstructibleLowerShriek ℓ g').obj M) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ g').hom.app M := by
  have inv_assoc (a : X' ⟶ Y') (b : Y' ⟶ Y) :
      (boundedConstructibleLowerShriekCompToPoint ℓ b).hom.app
          ((boundedConstructibleLowerShriek ℓ a).obj M) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ a).hom.app M =
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).inv.app M) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ (a ≫ b)).hom.app M := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekCompToPoint ℓ a).inv.app M ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ b).inv.app
        ((boundedConstructibleLowerShriek ℓ a).obj M))]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rw [← reassoc_of% (boundedConstructibleLowerShriekCompToPoint_assoc ℓ a b M),
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app]
  have inv_assoc' (a : X' ⟶ X) (b : X ⟶ Y) :
      (boundedConstructibleLowerShriekCompToPoint ℓ b).hom.app
          ((boundedConstructibleLowerShriek ℓ a).obj M) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ a).hom.app M =
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ a b).inv.app M) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ (a ≫ b)).hom.app M := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekCompToPoint ℓ a).inv.app M ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ b).inv.app
        ((boundedConstructibleLowerShriek ℓ a).obj M))]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rw [← reassoc_of% (boundedConstructibleLowerShriekCompToPoint_assoc ℓ a b M),
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app]
  rw [inv_assoc, inv_assoc', boundedConstructibleLowerShriekSquareIso_padicAlgCl]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (boundedConstructibleLowerShriek ℓ
      (toPoint Y)) ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ f' g).hom.app M),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    boundedConstructibleLowerShriekCompToPoint_hom_app_congr ℓ w]

/-- **The pullback on compactly supported cohomology commutes with compact-support base change**
(the unit compatibility of the mate `Ex_!`, blueprint `lemma-comparison-via-relative-frobenius--4`,
step (β)): for a cartesian square `g' ≫ f = f' ≫ g` with `g, g'` proper,
`c_{f'} ∘ RΓ_c(Ex_!) ∘ g^♯ = g'^♯ ∘ c_f`. -/
lemma compactPullback_app_comp_baseChange (sq : IsPullback g' f' f g) [IsProper g.left]
    [IsProper g'.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ g).app
        ((boundedConstructibleLowerShriek ℓ f).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y')).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ f').hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj K) =
    (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K ≫
      (compactPullback ℓ g').app K := by
  have hM := unit_mateEquiv_symm
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ g')
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ g)
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ sq.w).hom K
  rw [← boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv ℓ sq] at hM
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.id_obj, Functor.comp_obj, Functor.map_comp, Category.assoc] at hM
  have hM' := congrArg
    (boundedConstructibleLowerShriek ℓ (toPoint Y)).map hM
  simp only [Functor.map_comp] at hM'
  have hn := (boundedConstructibleLowerShriekCompToPoint ℓ g).hom.naturality
    ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K)
  have hn' := (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
      g').unit.app K ≫ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g').inv.app _)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hn hn'
  rw [compactPullback_app, compactPullback_app]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← reassoc_of% hM', boundedConstructibleLowerShriekSquareIso_compToPoint,
    reassoc_of% hn']

end BaseChange

/-! ### Frobenius coefficient morphisms -/

section Frobenius

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {Φ : X ⟶ X}

section Iterate

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {K : Dᵇc(X.left)⟦Λ⟧}

variable {ℓ} in
/-- The iterates `ψ_m : LΦ_m^* K ⟶ K` of a *Frobenius coefficient morphism* `ψ : LΦ^* K ⟶ K`,
an arbitrary morphism (blueprint `definition-frobenius-correspondences-their-operators`), for any
coefficient ring `Λ`: `ψ_0` is the identity isomorphism `L(𝟙 X)^* K ≅ K` and `ψ_{m+1}` is the
composite
```
LΦ_{m+1}^* K = L(Φ ≫ Φ_m)^* K ≅ LΦ^* LΦ_m^* K --LΦ^* ψ_m--> LΦ^* K --ψ--> K.
```
For the structure isomorphism of a Weil object these are the iterated Weil structures
(`ProEtale.CondensedRing.WeilBoundedConstructible.iterateStr_hom_eq_frobeniusCoefficientIterate`).
-/
noncomputable def frobeniusCoefficientIterate
    (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K) :
    (m : ℕ) → (boundedConstructibleUpperStar Λ ℓ (frobeniusIterate Φ m)).obj K ⟶ K
  | 0 => eqToHom (by rw [frobeniusIterate_zero]) ≫
    (boundedConstructibleUpperStarId Λ ℓ X).hom.app K
  | m + 1 =>
    eqToHom (by rw [frobeniusIterate_succ]) ≫
      (boundedConstructibleUpperStarComp Λ ℓ Φ (frobeniusIterate Φ m)).hom.app K ≫
      (boundedConstructibleUpperStar Λ ℓ Φ).map (frobeniusCoefficientIterate ψ m) ≫ ψ

variable {ℓ} in
lemma frobeniusCoefficientIterate_one (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K) :
    frobeniusCoefficientIterate ψ 1 = eqToHom (by rw [frobeniusIterate_one]) ≫ ψ := by
  have h := boundedConstructibleUpperStarComp_id_right_aux Λ ℓ
    (frobeniusIterate_zero Φ) (by rw [frobeniusIterate_zero, Category.comp_id]) ψ
  simp only [frobeniusCoefficientIterate]
  conv_rhs => rw [← h]
  rw [eqToHom_trans_assoc]

end Iterate

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- The iterates `Φ_m` of a proper endomorphism are proper. -/
instance isProper_frobeniusIterate [IsProper Φ.left] (m : ℕ) :
    IsProper (frobeniusIterate Φ m).left := by
  induction m with
  | zero => exact inferInstanceAs (IsProper (𝟙 X.left))
  | succ m ih =>
    rw [frobeniusIterate_succ, Over.comp_left]
    infer_instance

/-- The *global operator in degree `m`* `F_{c,m}(ψ) = T_{c_m}(ψ_m)` of a Frobenius coefficient
morphism `ψ : LΦ^* K ⟶ K` for a proper `Φ` (blueprint
`definition-frobenius-correspondences-their-operators`), in the form of
`definition-frobenius-correspondences-their-operators--5`:
```
RΓ_c(X, K) --Φ_m^♯--> RΓ_c(X, LΦ_m^* K) --RΓ_c(X, ψ_m)--> RΓ_c(X, K).
```
It is the global operator of the graph correspondence `(𝟙 X, Φ_m)` with coefficient map `ψ_m`
(`ProEtale.CondensedRing.Correspondence.globalOperator_frobeniusGraph`). -/
noncomputable def frobeniusCompactOperator [IsProper Φ.left]
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj K :=
  (compactPullback ℓ (frobeniusIterate Φ m)).app K ≫
    (boundedConstructibleLowerShriek ℓ (toPoint X)).map
      (frobeniusCoefficientIterate ψ m)

lemma frobeniusCompactOperator_zero [IsProper Φ.left]
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    frobeniusCompactOperator ℓ ψ 0 = 𝟙 _ := by
  have : IsProper (𝟙 X : X ⟶ X).left := inferInstanceAs (IsProper (𝟙 X.left))
  simp only [frobeniusCompactOperator, frobeniusCoefficientIterate]
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
    compactPullback_app_congr ℓ (frobeniusIterate_zero Φ), compactPullback_id_app,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rfl

lemma frobeniusCompactOperator_one [IsProper Φ.left]
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K) :
    frobeniusCompactOperator ℓ ψ 1 =
      (compactPullback ℓ Φ).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map ψ := by
  rw [frobeniusCompactOperator, frobeniusCoefficientIterate_one, Functor.map_comp,
    ← Category.assoc, compactPullback_app_congr ℓ (frobeniusIterate_one Φ)]

lemma frobeniusCompactOperator_succ [IsProper Φ.left]
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    frobeniusCompactOperator ℓ ψ (m + 1) =
      frobeniusCompactOperator ℓ ψ m ≫ frobeniusCompactOperator ℓ ψ 1 := by
  have : IsProper (Φ ≫ frobeniusIterate Φ m).left := by
    rw [Over.comp_left]
    infer_instance
  rw [frobeniusCompactOperator_one, frobeniusCompactOperator, frobeniusCompactOperator,
    ← compactPullback_app_congr ℓ (frobeniusIterate_succ Φ m).symm, frobeniusCoefficientIterate,
    compactPullback_comp_app]
  simp only [Category.assoc, ← Functor.map_comp, eqToHom_refl,
    Category.id_comp, Iso.inv_hom_id_app_assoc]
  rw [Functor.map_comp, compactPullback_naturality_assoc]

/-- **Iteration of the global operator** (blueprint `lemma-comparison-via-relative-frobenius--2`,
for an arbitrary Frobenius coefficient morphism): `F_{c,m}(ψ) = F_{c,1}(ψ)^m`. -/
lemma frobeniusCompactOperator_eq_pow [IsProper Φ.left]
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    (m : ℕ) :
    frobeniusCompactOperator ℓ ψ m =
      (End.of (frobeniusCompactOperator ℓ ψ 1) ^ m).asHom := by
  induction m with
  | zero => exact frobeniusCompactOperator_zero ℓ ψ
  | succ m ih =>
    rw [frobeniusCompactOperator_succ, ih, pow_succ']
    rfl

end Frobenius

namespace WeilBoundedConstructible

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {Φ : X ⟶ X}

variable {ℓ} in
/-- The iterated Weil structures `φ_m` of a Weil object are the iterates of its structure
isomorphism `φ` as a Frobenius coefficient morphism (blueprint
`definition-frobenius-correspondences-their-operators`, example). -/
lemma iterateStr_hom_eq_frobeniusCoefficientIterate (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) :
    (K.iterateStr m).hom = frobeniusCoefficientIterate K.str.hom m := by
  induction m with
  | zero =>
    simp only [iterateStr, frobeniusCoefficientIterate, Iso.app_hom, eqToHom_refl,
      Category.id_comp]
  | succ m ih =>
    simp only [iterateStr, frobeniusCoefficientIterate, Iso.trans_hom, eqToIso.hom, Iso.app_hom,
      Functor.mapIso_hom, ih]

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
