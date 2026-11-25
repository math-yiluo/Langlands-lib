/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentExchangeFactor
public import WeilConjectures.TraceFormula.Specialization.DeformationUnitClass
public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteClosedExtension

/-!

# The exchange `ν_X` on a proper component in normal form: the bookkeeping

`ProEtale.CondensedRing.pointExchange_normalForm_aux` deduces, in arbitrary categories, the normal
form of `ν_X` on `Rg_* N` (`pointCompactSupportExchangeOfSeparated_app_lowerStar_normalForm`)
from

* the ambient identity of `ν_X` on pushforwards (hypothesis `hF1`, an instance of
  `pointCompactSupportExchangeOfSeparated_app_lowerStar_component_eq`);
* the identification of the generic and of the special compactification routes with the normal
  forms (hypotheses `hG` and `hS`);
* the composition law of the pushforward exchanges `χ_{phg} = χ_a` (hypothesis `hF3`);
* the descriptions of the `Dᵇc` exchanges `χ_g`, `χ_a` through the ambient ones (`hχg`, `hχa`);
* the definition of `ν_B` as the inverse exchange of `χ_a` (`hνB`).

The hypotheses `hG` and `hS` are in turn deduced from the normal forms of the compactification
routes (`compactificationRoute_toPoint_eq_normalForm`) by the abstract lemmas `genericRoute_aux`,
`specialRoute_aux` and `specialNormalForm_aux`.

The tactics `fo_apply` and `fo_have` of `WeilConjectures.Tactic.FirstOrderApply` (first-order
instantiation of a lemma, with the given proofs transported along congruence proofs of the
equalities of their types) let the kernel check these instances of the abstract lemmas without
unfolding the large terms.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- **The bookkeeping of the normal form of `ν_X` on `Rg_* N`**, in arbitrary categories (see the
module docstring). -/
theorem pointExchange_normalForm_aux
    {CB CX CX' CB' Cs Cs' DB DB' DX DX' DY' DP' Ds Ds' : Type*} {_ : Category CB}
    {_ : Category CX} {_ : Category CX'} {_ : Category CB'} {_ : Category Cs}
    {_ : Category Cs'} {_ : Category DB} {_ : Category DB'} {_ : Category DX}
    {_ : Category DX'} {_ : Category DY'} {_ : Category DP'} {_ : Category Ds}
    {_ : Category Ds'}
    {G : CB ⥤ CX} {SpX : CX ⥤ CX'} {LSX : CX ⥤ Cs} {LSX' : CX' ⥤ Cs'} {Ts : Cs ⥤ Cs'}
    {SB : CB ⥤ CB'} {G'' : CB' ⥤ CX'} {LSg : CB ⥤ CX} {LSg'' : CB' ⥤ CX'}
    {LSB RaB : CB ⥤ Cs} {LSB'' RaB'' : CB' ⥤ Cs'}
    (νX : SpX ⋙ LSX' ⟶ LSX ⋙ Ts) (χgB : G ⋙ SpX ⟶ SB ⋙ G'')
    (isoG : LSg ≅ G) (lcG : LSB ≅ LSg ⋙ LSX) (isoG'' : LSg'' ≅ G'')
    (lcG'' : LSB'' ≅ LSg'' ⋙ LSX') (isoB : LSB ≅ RaB) (isoB'' : LSB'' ≅ RaB'')
    (χa : RaB ⋙ Ts ⟶ SB ⋙ RaB'') (hχiso : IsIso χa)
    (νB : SB ⋙ LSB'' ⟶ LSB ⋙ Ts) (hνB : νB = invExchange isoB isoB'' χa)
    {ιB : CB ⥤ DB} {ιB' : CB' ⥤ DB'} {ιX' : CX' ⥤ DX'} {ιs : Cs ⥤ Ds} {ιs' : Cs' ⥤ Ds'}
    (hι : ιs'.Faithful)
    {Ψs : Ds ⥤ Ds'} {ΨB : DB ⥤ DB'} (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs) (cSB : SB ⋙ ιB' ≅ ιB ⋙ ΨB)
    {Rphg RaBA : DB ⥤ Ds} {Rphg' RaB''A : DB' ⥤ Ds'}
    (χphg : Rphg ⋙ Ψs ⟶ ΨB ⋙ Rphg') (χaA : RaBA ⋙ Ψs ⟶ ΨB ⋙ RaB''A)
    (cAB : RaB ⋙ ιs ≅ ιB ⋙ RaBA) (cAB'' : RaB'' ⋙ ιs' ≅ ιB' ⋙ RaB''A) (N : CB)
    (eg : Rphg.obj (ιB.obj N) ⟶ RaBA.obj (ιB.obj N))
    (e' : Rphg'.obj (ΨB.obj (ιB.obj N)) ⟶ RaB''A.obj (ΨB.obj (ιB.obj N)))
    (e'' : Rphg'.obj (ιB'.obj (SB.obj N)) ⟶ RaB''A.obj (ιB'.obj (SB.obj N)))
    (hnat : Rphg'.map (cSB.hom.app N) ≫ e' = e'' ≫ RaB''A.map (cSB.hom.app N))
    (hχa : ιs'.map (χa.app N) = cT.hom.app (RaB.obj N) ≫ Ψs.map (cAB.hom.app N) ≫
      χaA.app (ιB.obj N) ≫ RaB''A.map (cSB.inv.app N) ≫ cAB''.inv.app (SB.obj N))
    (hF3 : χphg.app (ιB.obj N) ≫ e' = Ψs.map eg ≫ χaA.app (ιB.obj N))
    (Zg : ιs.obj (LSX.obj (G.obj N)) ⟶ Rphg.obj (ιB.obj N))
    (hG : Zg ≫ eg =
      ιs.map ((LSX.map (isoG.inv.app N) ≫ lcG.inv.app N) ≫ isoB.hom.app N) ≫ cAB.hom.app N)
    {Rg : DB ⥤ DX} {ΨX : DX ⥤ DX'} {Rg'' : DB' ⥤ DX'} {Dh₁ : DX' ⥤ DY'} {Dh₂ : DY' ⥤ DP'}
    {RP : DP' ⥤ Ds'} {Rg1 : DB' ⥤ DY'} {Rg2 : DB' ⥤ DP'}
    (χgA : Rg ⋙ ΨX ⟶ ΨB ⋙ Rg'') (cG'' : G'' ⋙ ιX' ≅ ιB' ⋙ Rg'')
    (cE₁ : Rg'' ⋙ Dh₁ ⟶ Rg1) (cE₂ : Rg1 ⋙ Dh₂ ⟶ Rg2) (lsc' : Rphg' ≅ Rg2 ⋙ RP)
    {W4 : DX'} (c3 : ιX'.obj (SpX.obj (G.obj N)) ⟶ W4) (c4 : W4 ⟶ ΨX.obj (Rg.obj (ιB.obj N)))
    (hχg : ιX'.map (χgB.app N) = c3 ≫ c4 ≫ χgA.app (ιB.obj N) ≫ Rg''.map (cSB.inv.app N) ≫
      cG''.inv.app (SB.obj N))
    {O : Cs'} (I₁ : O ⟶ LSX'.obj (SpX.obj (G.obj N))) (hI : IsIso I₁)
    {W1 : DP'} {W2 : DY'} (cA'h : ιs'.obj O ⟶ RP.obj W1) (c1 : W1 ⟶ Dh₂.obj W2)
    (c2 : W2 ⟶ Dh₁.obj (ιX'.obj (SpX.obj (G.obj N))))
    (hF1 : ιs'.map I₁ ≫ ιs'.map (νX.app (G.obj N)) ≫ cT.hom.app (LSX.obj (G.obj N)) ≫
        Ψs.map Zg ≫ χphg.app (ιB.obj N) =
      cA'h ≫ RP.map (c1 ≫ Dh₂.map c2 ≫ Dh₂.map (Dh₁.map c3) ≫ Dh₂.map (Dh₁.map c4) ≫
        Dh₂.map (Dh₁.map (χgA.app (ιB.obj N))) ≫ Dh₂.map (cE₁.app (ΨB.obj (ιB.obj N))) ≫
        cE₂.app (ΨB.obj (ιB.obj N))) ≫ lsc'.inv.app (ΨB.obj (ιB.obj N)))
    (hS : cA'h ≫ RP.map (c1 ≫ Dh₂.map c2 ≫ Dh₂.map (Dh₁.map (ιX'.map (χgB.app N))) ≫
        Dh₂.map (Dh₁.map (cG''.hom.app (SB.obj N))) ≫
        Dh₂.map (cE₁.app (ιB'.obj (SB.obj N))) ≫ cE₂.app (ιB'.obj (SB.obj N))) ≫
        lsc'.inv.app (ιB'.obj (SB.obj N)) ≫ e'' =
      ιs'.map (I₁ ≫ LSX'.map (χgB.app N) ≫ LSX'.map (isoG''.inv.app (SB.obj N)) ≫
        lcG''.inv.app (SB.obj N) ≫ isoB''.hom.app (SB.obj N)) ≫ cAB''.hom.app (SB.obj N)) :
    νX.app (G.obj N) ≫ Ts.map (LSX.map (isoG.inv.app N) ≫ lcG.inv.app N) =
      LSX'.map (χgB.app N) ≫ (LSX'.map (isoG''.inv.app (SB.obj N)) ≫
        lcG''.inv.app (SB.obj N) ≫ νB.app N) := by
  subst hνB
  -- the special route, with `χ_g` moved to the front
  have h5 : c3 ≫ c4 ≫ χgA.app (ιB.obj N) = ιX'.map (χgB.app N) ≫ cG''.hom.app (SB.obj N) ≫
      Rg''.map (cSB.hom.app N) := by
    rw [hχg]
    simp
  have n1 := cE₁.naturality (cSB.hom.app N)
  have n2 := cE₂.naturality (cSB.hom.app N)
  have n3 := lsc'.inv.naturality (cSB.hom.app N)
  have n4 := hnat
  simp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3
  have m1 : RP.map (Dh₂.map (Dh₁.map (Rg''.map (cSB.hom.app N)))) ≫
        RP.map (Dh₂.map (cE₁.app (ΨB.obj (ιB.obj N)))) =
      RP.map (Dh₂.map (cE₁.app (ιB'.obj (SB.obj N)))) ≫
        RP.map (Dh₂.map (Rg1.map (cSB.hom.app N))) := by
    rw [← RP.map_comp, ← Dh₂.map_comp, n1, Dh₂.map_comp, RP.map_comp]
  have m2 : RP.map (Dh₂.map (Rg1.map (cSB.hom.app N))) ≫ RP.map (cE₂.app (ΨB.obj (ιB.obj N))) =
      RP.map (cE₂.app (ιB'.obj (SB.obj N))) ≫ RP.map (Rg2.map (cSB.hom.app N)) := by
    rw [← RP.map_comp, n2, RP.map_comp]
  have m0 := congrArg (fun t ↦ RP.map (Dh₂.map (Dh₁.map t))) h5
  simp only [Functor.map_comp] at m0
  have hZs : (cA'h ≫ RP.map (c1 ≫ Dh₂.map c2 ≫ Dh₂.map (Dh₁.map c3) ≫ Dh₂.map (Dh₁.map c4) ≫
        Dh₂.map (Dh₁.map (χgA.app (ιB.obj N))) ≫ Dh₂.map (cE₁.app (ΨB.obj (ιB.obj N))) ≫
        cE₂.app (ΨB.obj (ιB.obj N))) ≫ lsc'.inv.app (ΨB.obj (ιB.obj N))) ≫
        e' ≫ RaB''A.map (cSB.inv.app N) =
      ιs'.map (I₁ ≫ LSX'.map (χgB.app N) ≫ LSX'.map (isoG''.inv.app (SB.obj N)) ≫
        lcG''.inv.app (SB.obj N) ≫ isoB''.hom.app (SB.obj N)) ≫ cAB''.hom.app (SB.obj N) := by
    rw [← hS]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% m0, reassoc_of% m1, reassoc_of% m2, reassoc_of% n3, reassoc_of% n4,
      ← RaB''A.map_comp, Iso.hom_inv_id_app]
    simp
  -- the generic route
  have hTs {Y Z : Cs} (f : Y ⟶ Z) :
      ιs'.map (Ts.map f) = cT.hom.app Y ≫ Ψs.map (ιs.map f) ≫ cT.inv.app Z := by
    have := cT.hom.naturality f
    simp only [Functor.comp_map, Functor.comp_obj] at this
    rw [← reassoc_of% this]
    simp
  have hG' : Ψs.map (ιs.map ((LSX.map (isoG.inv.app N) ≫ lcG.inv.app N) ≫ isoB.hom.app N)) ≫
      Ψs.map (cAB.hom.app N) ≫ χaA.app (ιB.obj N) =
      Ψs.map Zg ≫ χphg.app (ιB.obj N) ≫ e' := by
    rw [hF3, ← Ψs.map_comp_assoc, ← hG, Ψs.map_comp_assoc]
  have key : νX.app (G.obj N) ≫
      Ts.map ((LSX.map (isoG.inv.app N) ≫ lcG.inv.app N) ≫ isoB.hom.app N) ≫ χa.app N =
      LSX'.map (χgB.app N) ≫ LSX'.map (isoG''.inv.app (SB.obj N)) ≫
        lcG''.inv.app (SB.obj N) ≫ isoB''.hom.app (SB.obj N) := by
    apply hι.map_injective
    have : IsIso (ιs'.map I₁) := by
      have := hI
      infer_instance
    rw [ιs'.map_comp I₁] at hZs
    generalize (LSX.map (isoG.inv.app N) ≫ lcG.inv.app N) ≫ isoB.hom.app N = b₀ at hG' ⊢
    rw [← cancel_epi (ιs'.map I₁), ← cancel_mono (cAB''.hom.app (SB.obj N)),
      ← hZs]
    simp only [Functor.map_comp, Category.assoc]
    rw [hTs, hχa]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [reassoc_of% hG']
    simp only [← Category.assoc] at hF1 ⊢
    rw [hF1]
    simp
  simp only [invExchange, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatIso.isIso_inv_app]
  rw [← reassoc_of% key]
  simp

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section ToPoint

variable {k : Type u} [Field k] {X Y B : Over (Spec (.of k))} (x : RationalPoint X) (u : X ⟶ Y)
  [IsOpenImmersion u.left] [IsProper Y.hom] (k' : Type u) [Field k'] [Algebra k k']
  {b : RationalPoint B} (g : B ⟶ X) (hbg : b ≫ g = x)

/-- The composite `𝒟_B ⟶ 𝒳 ⟶ 𝒴 ⟶ 𝒫 ⟶ S` of the exchange `ν_X` on pushforwards from `B` has the
total morphism of the structure map of the deformation of `B`. -/
lemma pointCompModelHom_pointComponentModelHom_total :
    (pointCompModelHom x u k' (pointComponentModelHom k' g hbg)).total =
      deformationTotalToTrait B b.left.ker k' := by
  have h : (pointCompModelHom x u k' (pointComponentModelHom k' g hbg)).total =
      ((deformationTotalMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
        deformationTotalMap u (ker_compatible_of_isOpenImmersion x u) k') ≫
        deformationTotalToCompactified Y (x ≫ u) k') ≫ compactifiedTotalToTrait Y (x ≫ u) k' :=
    rfl
  rw [h, Category.assoc, deformationTotalToCompactified_toTrait, Category.assoc,
    deformationTotalMap_toTrait, deformationTotalMap_toTrait]

/-- The composite `𝒟_B ⟶ 𝒳 ⟶ 𝒴 ⟶ 𝒫 ⟶ S` has the generic morphism of the structure map of the
deformation of `B`. -/
lemma pointCompModelHom_pointComponentModelHom_generic :
    (pointCompModelHom x u k' (pointComponentModelHom k' g hbg)).generic =
      pullback.snd (deformationTotalToTrait B b.left.ker k') (traitGenericPoint k') := by
  have h : (pointCompModelHom x u k' (pointComponentModelHom k' g hbg)).generic =
      ((deformationGenericMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k' ≫
        deformationGenericMap u (ker_compatible_of_isOpenImmersion x u) k') ≫
        deformationGenericToCompactified Y (x ≫ u) k') ≫
        compactifiedGenericToPoint Y (x ≫ u) k' :=
    rfl
  rw [h, Category.assoc, deformationGenericToCompactified_toPoint, Category.assoc,
    deformationGenericMap_snd, deformationGenericMap_snd]

omit [IsOpenImmersion u.left] [IsProper Y.hom] in
/-- The composite `B ⟶ X ⟶ Y ⟶ Y ⟶ s` of the underlying schemes is the structure map of `B`. -/
lemma pointCompModelHom_pointComponentModelHom_left :
    ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = (toPoint B).left := by
  rw [Category.comp_id, ← Over.comp_left, ← Over.comp_left, comp_toPoint]

/-- The composite `B_s ⟶ X_s ⟶ Y_s ⟶ P_s ⟶ s` of the special fibres is the structure map of the
special fibre of the deformation of `B`. -/
lemma pointCompModelHom_pointComponentModelHom_special :
    (((deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hbg) k').left ≫
        (pointSpecialMap x u k').left) ≫
        (deformationSpecialFibreToCompactified Y (x ≫ u) k').left) ≫
        (toPoint (compactifiedSpecialFibre Y (x ≫ u) k')).left =
      (toPoint (deformationSpecialFibre B b.left.ker k')).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_toPoint]

end ToPoint

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- `leftDerivedUpperStarCompOfEq` is `leftDerivedUpperStarComp` up to `eqToHom`. -/
lemma leftDerivedUpperStarCompOfEq_hom_app {B₀ B₁ B₂ : Scheme.{u}} (p : B₀ ⟶ B₁) (q : B₁ ⟶ B₂)
    {pq : B₀ ⟶ B₂} (w : p ≫ q = pq) (K : 𝔻(B₂)) :
    (leftDerivedUpperStarCompOfEq Λ w).hom.app K =
      eqToHom (by rw [w]) ≫ (leftDerivedUpperStarComp Λ p q).hom.app K := by
  subst w
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- For `f ≫ 𝟙 = f`, the inverse of `L(f)^* ≅ L(𝟙)^* ⋙ L(f)^*` is `L(f)^*(L(𝟙)^* ≅ 𝟭)`. -/
lemma leftDerivedUpperStarCompOfEq_comp_id_inv_app {B Y : Scheme.{u}} (f : B ⟶ Y)
    (w : f ≫ 𝟙 Y = f) (K : 𝔻(Y)) :
    (leftDerivedUpperStarCompOfEq Λ w).inv.app K =
      L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app K) := by
  have h := leftDerivedUpperStarComp_id_right_app Λ f K
  have h' : (leftDerivedUpperStarCompOfEq Λ w).hom.app K ≫
      L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app K) = 𝟙 _ := by
    rw [leftDerivedUpperStarCompOfEq_hom_app, Category.assoc, h, eqToHom_trans, eqToHom_refl]
  exact (((leftDerivedUpperStarCompOfEq Λ w).app K).hom_comp_eq_id.mp h').symm

/-- The closed base change along `f ≫ 𝟙 = f` is `L(𝟙)^* ≅ 𝟭` at `Rf_* N`. -/
lemma closedBaseChange_comp_id_app {B Y : Scheme.{u}} (f : B ⟶ Y) (w : f ≫ 𝟙 Y = f)
    (N : 𝔻(B)) :
    (closedBaseChange Λ w).app N = (leftDerivedUpperStarId Λ Y).hom.app (R((f)_*⟦Λ⟧).obj N) := by
  apply ((derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [map_closedBaseChange_app_comp_counit, leftDerivedUpperStarCompOfEq_comp_id_inv_app]

/-- The unit of the adjunction `𝟭 ⊣ L` given by an isomorphism `e : 𝟭 ≅ L`. -/
lemma Adjunction.id_ofNatIsoRight_unit_app {C : Type*} [Category C] {L : C ⥤ C} (e : 𝟭 C ≅ L)
    (X : C) : (Adjunction.id.ofNatIsoRight e).unit.app X = e.hom.app X := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit]
  simp

/-- For the adjunction `𝟭 ⊣ L` given by `e : 𝟭 ≅ L`, an endomorphism `c` whose adjoint is
inverse to `e⁻¹` is the identity. -/
lemma eq_id_of_unit_comp_map_comp {C : Type*} [Category C] {L : C ⥤ C} (e : 𝟭 C ≅ L) {X : C}
    (c : X ⟶ X) (b : L.obj X ⟶ X) (hb : b = e.inv.app X)
    (h : (Adjunction.id.ofNatIsoRight e).unit.app X ≫ L.map c ≫ b = 𝟙 _) : c = 𝟙 X := by
  have hn := e.inv.naturality c
  simp only [Functor.id_map] at hn
  rw [hb, Adjunction.id_ofNatIsoRight_unit_app, hn, Iso.hom_inv_id_app_assoc] at h
  exact h

/-- **`closedExtension` along the identity** (for `𝟭 ⊣ L(𝟙)^*`) is the identity, up to
`R(f ≫ 𝟙)_* = Rf_*`. -/
lemma closedExtension_id_app_of_eq {B Y : Scheme.{u}} (f : B ⟶ Y) {hg : B ⟶ Y}
    (w : f ≫ 𝟙 Y = hg) (hf : hg = f) (N : 𝔻(B)) :
    (closedExtension (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λ Y).symm) w).app N =
      (eqToHom (by rw [hf]) : R((f)_*⟦Λ⟧).obj N ⟶ R((hg)_*⟦Λ⟧).obj N) := by
  subst hf
  exact eq_id_of_unit_comp_map_comp _ _ _ (closedBaseChange_comp_id_app _ w N)
    (unit_comp_closedExtension_app _ w N)

/-- Transporting the inverse composition isomorphism of the pushforwards along `f₁ = f₂`. -/
lemma map_eqToHom_comp_lowerStarCompOfEq_inv_app {B C Y : Scheme.{u}} {f₁ f₂ : B ⟶ C}
    (h : f₁ = f₂) (p : C ⟶ Y) (N : 𝔻(B)) :
    R((p)_*⟦Λ⟧).map (eqToHom (by rw [h]) : R((f₁)_*⟦Λ⟧).obj N ⟶ R((f₂)_*⟦Λ⟧).obj N) ≫
        (lowerStarCompOfEq (Λ := Λ) (rfl : f₂ ≫ p = _)).inv.app N =
      (lowerStarCompOfEq (Λ := Λ) (rfl : f₁ ≫ p = _)).inv.app N ≫ eqToHom (by rw [h]) := by
  subst h
  simp

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

section Generic

variable {B X Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The compactification route to the point in normal form**:
`compactificationRoute_eq_normalForm` for `Ra_{X!}` through the open `u : X ⟶ Y` into the
proper `Y`, with the transports along `g ≫ u ≫ a_Y = a_B` (`comp_toPoint`). -/
theorem compactificationRoute_toPoint_eq_normalForm (g : B ⟶ X) (u : X ⟶ Y)
    [IsOpenImmersion u.left] [IsProper (toPoint Y).left] [IsProper g.left] [IsProper (g ≫ u).left]
    [IsProper ((g ≫ u) ≫ toPoint Y).left] [IsProper (g ≫ toPoint X).left]
    [IsProper (toPoint B).left] (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (compactificationLowerShriekIso ℓ u (toPoint Y) (comp_toPoint u)).hom.app
        ((boundedConstructibleLowerStar ℓ g).obj N) ≫
      (boundedConstructibleLowerStar ℓ (toPoint Y)).map ((openProperExtension ℓ g u).hom.app N) ≫
      (boundedConstructibleLowerStarComp ℓ (g ≫ u) (toPoint Y)).hom.app N ≫
      eqToHom (by rw [comp_toPoint]) =
    ((boundedConstructibleLowerShriek ℓ (toPoint X)).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).inv.app N) ≫
      (lowerShriekCompOfEq ℓ g (toPoint X) (comp_toPoint g)).inv.app N) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint B)).hom.app N := by
  have h := compactificationRoute_eq_normalForm ℓ g u (toPoint Y) (comp_toPoint u) N
  have h' := eqToHom_isoLowerStar_hom_app_eqToHom ℓ (rfl : g ≫ toPoint X = _) (comp_toPoint g) N
  rw [eqToHom_refl, Category.id_comp] at h'
  simp only [lowerShriekCompOfEq, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app,
    Category.assoc]
  rw [← h', ← reassoc_of% h, eqToHom_trans]

/-- `eqToHom` along an equality of functors commutes with their actions on morphisms. -/
lemma functor_map_comp_eqToHom_of_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (h : F = G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ eqToHom (Functor.congr_obj h Y) = eqToHom (Functor.congr_obj h X) ≫ G.map f := by
  subst h
  simp

/-- **The special compactification route of `ν_X`**, read through the inclusions of `Dᵇc`, in
abstract categories: for `Dᵇc` functors which are lifts of ambient functors, the ambient route
`ι(...) ≫ RP(D₂(D₁(ι χ)) ≫ D₂(cE₁) ≫ cE₂) ≫ lsc⁻¹ ≫ eqToHom` is `ι` of its `Dᵇc` normal form,
given that the ambient extensions `cE₁`, `cE₂` and composition `lsc` restrict to the `Dᵇc` ones
(`s1`, `s2`, `s3`) and the normal form `s6` on `Dᵇc`. -/
theorem specialRoute_aux {DC DY DP Ds DB : Type*} {_ : Category DC} {_ : Category DY}
    {_ : Category DP} {_ : Category Ds} {_ : Category DB}
    {PC : ObjectProperty DC} {PY : ObjectProperty DY} {PP : ObjectProperty DP}
    {Ps : ObjectProperty Ds} {PB : ObjectProperty DB}
    {D1 : DC ⥤ DY} {D2 : DY ⥤ DP} {RP : DP ⥤ Ds} {Rg : DB ⥤ DC} {Rg1 : DB ⥤ DY}
    {Rg2 : DB ⥤ DP} {Rall RB : DB ⥤ Ds}
    {hD1 : ∀ X, PY ((PC.ι ⋙ D1).obj X)} {hD2 : ∀ X, PP ((PY.ι ⋙ D2).obj X)}
    {hRP : ∀ X, Ps ((PP.ι ⋙ RP).obj X)} {hG : ∀ X, PC ((PB.ι ⋙ Rg).obj X)}
    {hG1 : ∀ X, PY ((PB.ι ⋙ Rg1).obj X)} {hG2 : ∀ X, PP ((PB.ι ⋙ Rg2).obj X)}
    {hall : ∀ X, Ps ((PB.ι ⋙ Rall).obj X)} {hB : ∀ X, Ps ((PB.ι ⋙ RB).obj X)}
    {Z : PC.FullSubcategory} {M : PB.FullSubcategory}
    {χ : Z ⟶ (PC.lift (PB.ι ⋙ Rg) hG).obj M}
    {oPE1 : (PY.lift (PC.ι ⋙ D1) hD1).obj ((PC.lift (PB.ι ⋙ Rg) hG).obj M) ⟶
      (PY.lift (PB.ι ⋙ Rg1) hG1).obj M}
    {oPE2 : (PP.lift (PY.ι ⋙ D2) hD2).obj ((PY.lift (PB.ι ⋙ Rg1) hG1).obj M) ⟶
      (PP.lift (PB.ι ⋙ Rg2) hG2).obj M}
    {compN : PP.lift (PB.ι ⋙ Rg2) hG2 ⋙ Ps.lift (PP.ι ⋙ RP) hRP ≅ Ps.lift (PB.ι ⋙ Rall) hall}
    {cE₁ : Rg ⋙ D1 ⟶ Rg1} (s1 : cE₁.app M.obj = oPE1.hom)
    {cE₂ : Rg1 ⋙ D2 ⟶ Rg2} (s2 : cE₂.app M.obj = oPE2.hom)
    {lsc : Rall ≅ Rg2 ⋙ RP} (s3 : (compN.inv.app M).hom = lsc.hom.app M.obj)
    {LSX' : PC.FullSubcategory ⥤ Ps.FullSubcategory} {LSg : PB.FullSubcategory ⥤ PC.FullSubcategory}
    {LSB : PB.FullSubcategory ⥤ Ps.FullSubcategory}
    {I₁ : (Ps.lift (PP.ι ⋙ RP) hRP).obj ((PP.lift (PY.ι ⋙ D2) hD2).obj
      ((PY.lift (PC.ι ⋙ D1) hD1).obj Z)) ⟶ LSX'.obj Z}
    {isoGi : (PC.lift (PB.ι ⋙ Rg) hG).obj M ⟶ LSg.obj M} {lcGi : LSX'.obj (LSg.obj M) ⟶ LSB.obj M}
    {isoBh : LSB.obj M ⟶ (Ps.lift (PB.ι ⋙ RB) hB).obj M}
    {hq : (Ps.lift (PB.ι ⋙ Rall) hall).obj M = (Ps.lift (PB.ι ⋙ RB) hB).obj M}
    (s6 : (Ps.lift (PP.ι ⋙ RP) hRP).map ((PP.lift (PY.ι ⋙ D2) hD2).map
        ((PY.lift (PC.ι ⋙ D1) hD1).map χ) ≫ (PP.lift (PY.ι ⋙ D2) hD2).map oPE1 ≫ oPE2) ≫
        compN.hom.app M ≫ eqToHom hq = I₁ ≫ LSX'.map χ ≫ LSX'.map isoGi ≫ lcGi ≫ isoBh)
    (h'' : Rall.obj M.obj = RB.obj M.obj) :
    (Ps.liftCompιIso (PP.ι ⋙ RP) hRP).hom.app ((PP.lift (PY.ι ⋙ D2) hD2).obj
        ((PY.lift (PC.ι ⋙ D1) hD1).obj Z)) ≫
      RP.map ((PP.liftCompιIso (PY.ι ⋙ D2) hD2).hom.app ((PY.lift (PC.ι ⋙ D1) hD1).obj Z) ≫
        D2.map ((PY.liftCompιIso (PC.ι ⋙ D1) hD1).hom.app Z) ≫ D2.map (D1.map (PC.ι.map χ)) ≫
        D2.map (D1.map ((PC.liftCompιIso (PB.ι ⋙ Rg) hG).hom.app M)) ≫
        D2.map (cE₁.app (PB.ι.obj M)) ≫ cE₂.app (PB.ι.obj M)) ≫
      lsc.inv.app (PB.ι.obj M) ≫ eqToHom h'' =
    Ps.ι.map (I₁ ≫ LSX'.map χ ≫ LSX'.map isoGi ≫ lcGi ≫ isoBh) ≫
      (Ps.liftCompιIso (PB.ι ⋙ RB) hB).hom.app M := by
  have s3' : lsc.inv.app M.obj = (compN.hom.app M).hom := by
    rw [← cancel_epi (lsc.hom.app M.obj), Iso.hom_inv_id_app, ← s3,
      ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
    rfl
  rw [← s6]
  simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  simp only [ObjectProperty.ι_obj, s1, s2, s3', Functor.map_comp, Category.assoc,
    ObjectProperty.ι_map]
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.lift_map,
    ObjectProperty.homMk_hom, CategoryTheory.Functor.map_id, Category.id_comp, Functor.comp_map,
    ObjectProperty.ι_map]
  rw [ObjectProperty.eqToHom_hom hq]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The special compactification route in normal form**, in abstract categories: for open
immersions `h₁ : X' ⟶ Y`, `h₂ : Y ⟶ P` and proper `g'' : B'' ⟶ X'`, the route
`Ra_{P*}(h₂!h₁!(χ) ≫ h₂!(φ₁) ≫ φ₂) ≫ (R(g''h₁h₂)_* ≅ ...)` (`φᵢ` the `openProperExtension`s,
`oPE1 = φ₁` unfolded in `hO1`) is `I₁ ≫ Ra_{X'!}(χ) ≫` the normal form of `g''`, given the normal
form `T1` of the route of `g'' ≫ h₁` through `h₂`, the associativity `hassoc` of the composition
isomorphisms of the lower shriek and the transport `htrans` along `h₁ ≫ a_Y = a_{X'}`. -/
theorem specialNormalForm_aux {CB CX CY CP Cs : Type*} {_ : Category CB} {_ : Category CX}
    {_ : Category CY} {_ : Category CP} {_ : Category Cs}
    {G : CB ⥤ CX} {G1 : CB ⥤ CY} {G2 : CB ⥤ CP} {Gall RaB : CB ⥤ Cs}
    {O1 : CX ⥤ CY} {O2 : CY ⥤ CP} {RaP : CP ⥤ Cs}
    {LS1 : CX ⥤ CY} {LS2 : CY ⥤ CP} {LSP : CP ⥤ Cs} {LSY : CY ⥤ Cs} {LSX LS1Y : CX ⥤ Cs}
    {LSg : CB ⥤ CX} {LSg1 : CB ⥤ CY} {LSB LSgX LSg1Y LSg_1Y : CB ⥤ Cs}
    {ιO1 : LS1 ≅ O1} {ιO2 : LS2 ≅ O2} {ιSP : LSP ≅ RaP} {ιSg : LSg ≅ G} {ιSg1 : LSg1 ≅ G1}
    {ιSB : LSB ≅ RaB} {C1 : LSg1 ≅ LSg ⋙ LS1} {lc2 : LSY ≅ LS2 ⋙ LSP}
    {lc1 : LSX ≅ LS1 ⋙ LSY} {e1 : LSX = LS1Y} {C1Y : LS1Y ≅ LS1 ⋙ LSY}
    (hlc1 : lc1 = eqToIso e1 ≪≫ C1Y)
    {lcg : LSB ≅ LSg ⋙ LSX} {eg : LSB = LSgX} {CgX : LSgX ≅ LSg ⋙ LSX}
    (hlcg : lcg = eqToIso eg ≪≫ CgX)
    {lcg1 : LSB ≅ LSg1 ⋙ LSY} {eg1 : LSB = LSg1Y} {Cg1Y : LSg1Y ≅ LSg1 ⋙ LSY}
    (hlcg1 : lcg1 = eqToIso eg1 ≪≫ Cg1Y) {Cg_1Y : LSg_1Y ≅ LSg ⋙ LS1Y}
    {Z : CX} {M : CB} (χ : Z ⟶ G.obj M) {oPE1 : O1.obj (G.obj M) ⟶ G1.obj M}
    (hO1 : oPE1 = ιO1.inv.app (G.obj M) ≫ LS1.map (ιSg.inv.app M) ≫ C1.inv.app M ≫
      ιSg1.hom.app M)
    {compN : G2 ⋙ RaP ≅ Gall} {oPE2 : O2.obj (G1.obj M) ⟶ G2.obj M}
    {hT : Gall.obj M = RaB.obj M}
    (T1 : (lc2 ≪≫ Functor.isoWhiskerRight ιO2 LSP ≪≫ Functor.isoWhiskerLeft O2 ιSP).hom.app
        (G1.obj M) ≫ RaP.map oPE2 ≫ compN.hom.app M ≫ eqToHom hT =
      (LSY.map (ιSg1.inv.app M) ≫ lcg1.inv.app M) ≫ ιSB.hom.app M)
    {eA : LSg_1Y.obj M = LSg1Y.obj M}
    (hassoc : C1Y.hom.app (LSg.obj M) ≫ LSY.map (C1.inv.app M) ≫ Cg1Y.inv.app M =
      Cg_1Y.inv.app M ≫ eqToHom eA)
    {eT1 : LS1Y.obj (LSg.obj M) = LSX.obj (LSg.obj M)} {eT2 : LSg_1Y.obj M = LSgX.obj M}
    (htrans : eqToHom eT1 ≫ LSX.map (𝟙 (LSg.obj M)) ≫ CgX.inv.app M =
      LS1Y.map (𝟙 (LSg.obj M)) ≫ Cg_1Y.inv.app M ≫ eqToHom eT2) :
    RaP.map (O2.map (O1.map χ) ≫ O2.map oPE1 ≫ oPE2) ≫ compN.hom.app M ≫ eqToHom hT =
    (ιSP.inv.app (O2.obj (O1.obj Z)) ≫ LSP.map (ιO2.inv.app (O1.obj Z)) ≫
        lc2.inv.app (O1.obj Z) ≫ (lc1 ≪≫ Functor.isoWhiskerRight ιO1 LSY).inv.app Z) ≫
      LSX.map χ ≫ LSX.map (ιSg.inv.app M) ≫ lcg.inv.app M ≫ ιSB.hom.app M := by
  subst hlc1 hlcg hlcg1 e1 eg eg1
  have key : CgX.inv.app M = C1Y.hom.app (LSg.obj M) ≫ LSY.map (C1.inv.app M) ≫
      Cg1Y.inv.app M := by
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp] at htrans
    rw [htrans, hassoc]
  have T1' : RaP.map oPE2 ≫ compN.hom.app M ≫ eqToHom hT =
      (lc2 ≪≫ Functor.isoWhiskerRight ιO2 LSP ≪≫ Functor.isoWhiskerLeft O2 ιSP).inv.app
        (G1.obj M) ≫ (LSY.map (ιSg1.inv.app M) ≫ (eqToIso rfl ≪≫ Cg1Y).inv.app M) ≫
        ιSB.hom.app M := by
    rw [← T1, Iso.inv_hom_id_app_assoc]
  have nat :=
    (lc2 ≪≫ Functor.isoWhiskerRight ιO2 LSP ≪≫ Functor.isoWhiskerLeft O2 ιSP).inv.naturality
      (O1.map χ ≫ oPE1)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, T1',
    ← Functor.map_comp_assoc, ← Functor.map_comp, reassoc_of% nat]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToIso_refl,
    Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.assoc, Functor.map_comp, key, Iso.inv_hom_id_app_assoc, hO1,
    ← Functor.comp_map, ← C1Y.inv.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← LSY.map_comp_assoc (ιO1.inv.app Z), ← ιO1.inv.naturality, Functor.map_comp_assoc,
    ← LSY.map_comp_assoc (ιSg1.hom.app M), Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- **The generic compactification route of `ν_X` in normal form**, in abstract categories: the
composite `ι(i ≫ i₄) ≫ c ≫ r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ l₁` (as in the ambient identity of `ν_X`), followed
by a transport, is `ι(V)` for the normal form `V`, given the ambient compactification route `g3`
(through `cLSI = i ≫ i₄`), the triviality of the extension along the identity (`g1`, `g2`) and the
normal form `g4` of the `Dᵇc` route. -/
theorem genericRoute_aux {Cs Ds : Type*} {_ : Category Cs} {_ : Category Ds} {ιs : Cs ⥤ Ds}
    {A0 A1 A2 A3 A4 A5 : Cs} {W1 W2 W3 W4 W5 W6 : Ds}
    {i_ : A0 ⟶ A1} {i4_ : A1 ⟶ A2} {cLSI_ : A0 ⟶ A2} (g5 : cLSI_ = i_ ≫ i4_)
    {c_ : ιs.obj A2 ⟶ W1} {r1 : W1 ⟶ W2} {r2 : W2 ⟶ W3} {r3 : W3 ⟶ W4} {r4 r4' : W4 ⟶ W5}
    (g1 : r4 = r4') {l0 : W4 ⟶ ιs.obj A4} {oPE_ : A2 ⟶ A3} {comp_ : A3 ⟶ A4}
    (g3 : ιs.map cLSI_ ≫ c_ ≫ r1 ≫ r2 ≫ r3 ≫ l0 = ιs.map (cLSI_ ≫ oPE_ ≫ comp_))
    {l1 : W5 ⟶ W6} {h₂ : ιs.obj A4 = W6} (g2 : r4' ≫ l1 = l0 ≫ eqToHom h₂)
    {h₃ : A4 = A5} {V : A0 ⟶ A5} (g4 : cLSI_ ≫ oPE_ ≫ comp_ ≫ eqToHom h₃ = V)
    {cABh : ιs.obj A5 ⟶ ιs.obj A5} (g7 : cABh = 𝟙 _) (hg : W6 = ιs.obj A5) :
    (ιs.map (i_ ≫ i4_) ≫ c_ ≫ r1 ≫ r2 ≫ r3 ≫ r4 ≫ l1) ≫ eqToHom hg = ιs.map V ≫ cABh := by
  subst g5 g1 g7 h₃ hg
  rw [Category.comp_id, ← g4]
  simp only [eqToHom_refl, Category.comp_id] at g2
  simp only [Category.assoc, Functor.map_comp, eqToHom_refl, Category.comp_id] at g3 ⊢
  rw [g2, g3]

/-- The components of `α ≪≫ β ⋙ H ≪≫ G₂ ⋙ γ` (the shape of `compactificationLowerShriekIso`). -/
lemma isoTrans_isoWhiskerLeft_hom_app {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ E} {G₁ G₂ : C ⥤ D} {H K : D ⥤ E} (α : F ≅ G₁ ⋙ H) (β : G₁ ≅ G₂) (γ : H ≅ K)
    (M : C) :
    (α ≪≫ Functor.isoWhiskerRight β H ≪≫ Functor.isoWhiskerLeft G₂ γ).hom.app M =
      (α ≪≫ Functor.isoWhiskerRight β H).hom.app M ≫ γ.hom.app (G₂.obj M) := by
  simp

end Generic
section Special

variable {B C P : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- The components of `openProperExtension`, unfolded. -/
lemma openProperExtension_hom_app_eq (a : B ⟶ C) (h : C ⟶ P) [IsOpenImmersion h.left]
    [IsProper a.left] [IsProper (a ≫ h).left] (N : Dᵇc(B.left)⟦Λℓ⟧) :
    (openProperExtension ℓ a h).hom.app N =
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ h).inv.app
          ((boundedConstructibleLowerStar ℓ a).obj N) ≫
        (boundedConstructibleLowerShriek ℓ h).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ a).inv.app N) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ a h).inv.app N ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (a ≫ h)).hom.app N :=
  rfl

/-- `lowerShriekCompOfEq`, unfolded. -/
lemma lowerShriekCompOfEq_eq_trans {a : B ⟶ P} (d : B ⟶ C) (b : C ⟶ P) (w : d ≫ b = a) :
    lowerShriekCompOfEq ℓ d b w =
      eqToIso (by rw [← w]) ≪≫ boundedConstructibleLowerShriekComp_padicAlgCl ℓ d b :=
  rfl

end Special

end AlgebraicGeometry.ProEtale.CondensedRing
