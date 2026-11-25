/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentClassReduction
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnSeparatedBdc

/-!

# Factoring the exchange of the fixed locus through a component: the proper pieces

This file proves the pieces of fact (II) of `ComponentClassReduction` (`ν_F(j_! ℚ̄_ℓ)` factors
through the inverse proper exchange `ν_B` of the deformation of the component `B`) which concern
the diagonal and the composition of the proper exchanges.

* `CategoryTheory.map_comp_mateEquiv_symm_app_comp_counit_comp` (**the diagonal step**): for the
  mate `α_Δ` of `χ_Δ` (as in `fixedSquareCompactSupportExchange`), if `t` factors as
  `Ψ_P(c) ≫ χ_Δ(G) ≫ Δ'_*(g)`, then `Δ'^*Ψ_P(c) ≫ α_Δ(Δ_* G) ≫ Ψ_X(ε_G) ≫ g = Δ'^*(t) ≫ ε'`.
* `Correspondence.IsContractingAt.componentSupportModelHom_pushforwardExchange_app` (**composition
  on the support side**): the pushforward exchange of `𝒟_B ⟶ 𝒞 ⟶ 𝒞̄ ⟶ 𝒳 ×_S 𝒳` (the composite
  `χ_{phg}` of `supportCompactSupportExchange_app_lowerStar` for `componentModelHom`) is that of
  `𝒟_B ⟶ 𝒳` over `d ∘ j` followed by that of the diagonal (`deformationDiagModelHom`), the morphisms
  of total spaces, generic and special fibres being identified
  (`componentPointModelHom_total_comp_diag`, `componentPointModelHom_generic_comp_diag`, …).
* `Correspondence.IsContractingAt.componentToPointModelHom_pushforwardExchange_app` (**composition
  on the point side**): the composite `𝒟_B ⟶ 𝒳 ⟶ 𝒳̄ ⟶ 𝒫 ⟶ S` (the `χ_{phg}` of
  `pointCompactSupportExchangeOfSeparated_app_lowerStar_component_eq` for `d ∘ j`) has the
  pushforward exchange of `deformationToTraitModelHom B (ker b)`, whose inverse is `ν_B`
  (`NearbyCyclesModel.Hom.pushforwardExchange_app_eq_of_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {DP DX DP' DX' : Type*} [Category DP] [Category DX] [Category DP'] [Category DX']
  {ΔU : DP ⥤ DX} {ΔS : DX ⥤ DP} {ΔU' : DP' ⥤ DX'} {ΔS' : DX' ⥤ DP'} (adjΔ : ΔU ⊣ ΔS)
  (adjΔ' : ΔU' ⊣ ΔS') {ΨP : DP ⥤ DP'} {ΨX : DX ⥤ DX'} (χΔ : ΔS ⋙ ΨP ⟶ ΨX ⋙ ΔS')

/-- **The diagonal step**: let `α_Δ : Δ'^* Ψ_P ⟶ Ψ_X Δ^*` be the mate of `χ_Δ`. If
`t : Ψ_P T ⟶ Δ'_* G'` factors as `Ψ_P(c) ≫ χ_Δ(G) ≫ Δ'_*(g)` for `c : T ⟶ Δ_* G` and
`g : Ψ_X G ⟶ G'` (the composition law of exchanges, for `T = (Δ ∘ g)_* E`, `G = g_* E`), then
`Δ'^* Ψ_P T ⟶ Δ'^* Ψ_P Δ_* G ⟶ Ψ_X Δ^* Δ_* G ⟶ Ψ_X G ⟶ G'` (`α_Δ`, the counit of `Δ`, `g`) is
`Δ'^*(t)` followed by the counit of `Δ'`. -/
lemma map_comp_mateEquiv_symm_app_comp_counit_comp {G : DX} {G' : DX'} {T : DP}
    (c : T ⟶ ΔS.obj G) (g : ΨX.obj G ⟶ G') (t : ΨP.obj T ⟶ ΔS'.obj G')
    (hcomp : t = ΨP.map c ≫ χΔ.app G ≫ ΔS'.map g) :
    ΔU'.map (ΨP.map c) ≫ ((mateEquiv adjΔ adjΔ').symm χΔ).app (ΔS.obj G) ≫
        ΨX.map (adjΔ.counit.app G) ≫ g = ΔU'.map t ≫ adjΔ'.counit.app G' := by
  have h := mateEquiv_counit_symm adjΔ adjΔ' χΔ G
  have hc := adjΔ'.counit.naturality g
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at h hc
  rw [hcomp, ← reassoc_of% h]
  simp only [Functor.map_comp, Category.assoc, hc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section TotalMap

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
  {X Y : Over (Spec (.of k))} {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData}

/-- A composite of three morphisms of total spaces along kernels of rational points is the morphism
of total spaces of the composite, written as any morphism equal to it. -/
lemma deformationTotalMap_comp_comp_of_eq {Z W : Over (Spec (.of k))}
    {I₃ : Z.left.IdealSheafData} {x : RationalPoint X} {w : RationalPoint W}
    (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (f₃ : Z ⟶ W) (g : X ⟶ W)
    (h₁ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f₁.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f₁.left.appLE U.1 U'.1 hU).hom ≤
        x.left.ker.siteIdeal U')
    (h₂ : ∀ ⦃U' : Y.left.AffineZariskiSite⦄ ⦃U : Z.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f₂.left ⁻¹ᵁ U.1), (I₃.siteIdeal U).map (f₂.left.appLE U.1 U'.1 hU).hom ≤
        I.siteIdeal U')
    (h₃ : ∀ ⦃U' : Z.left.AffineZariskiSite⦄ ⦃U : W.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f₃.left ⁻¹ᵁ U.1),
        (w.left.ker.siteIdeal U).map (f₃.left.appLE U.1 U'.1 hU).hom ≤
        I₃.siteIdeal U') (hg : x ≫ g = w) (e : f₁ ≫ f₂ ≫ f₃ = g) {yY : RationalPoint Y}
    (hI : I = yY.left.ker) (hy : yY ≫ f₂ ≫ f₃ = w) :
    (deformationTotalMap f₁ h₁ k' ≫ deformationTotalMap f₂ h₂ k') ≫
        deformationTotalMap f₃ h₃ k' =
      deformationTotalMap g (map_siteIdeal_ker_le_of_comp_eq g hg) k' := by
  subst hI
  rw [Category.assoc,
    deformationTotalMap_comp k' f₂ f₃ h₂ h₃ (map_siteIdeal_ker_le_of_comp_eq _ hy),
    deformationTotalMap_comp k' f₁ (f₂ ≫ f₃) h₁ _ (map_siteIdeal_ker_le_of_comp_eq _ (by
      rw [← hg, ← e]))]
  exact deformationTotalMap_eq_of_eq k' e _ _

/-- `deformationTotalMap_comp_comp_of_eq` for the morphisms of special fibres. -/
lemma deformationSpecialFibreMap_comp_comp_of_eq {Z W : Over (Spec (.of k))}
    {I₃ : Z.left.IdealSheafData} {x : RationalPoint X} {w : RationalPoint W}
    (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (f₃ : Z ⟶ W) (g : X ⟶ W)
    (h₁ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f₁.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f₁.left.appLE U.1 U'.1 hU).hom ≤
        x.left.ker.siteIdeal U')
    (h₂ : ∀ ⦃U' : Y.left.AffineZariskiSite⦄ ⦃U : Z.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f₂.left ⁻¹ᵁ U.1), (I₃.siteIdeal U).map (f₂.left.appLE U.1 U'.1 hU).hom ≤
        I.siteIdeal U')
    (h₃ : ∀ ⦃U' : Z.left.AffineZariskiSite⦄ ⦃U : W.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f₃.left ⁻¹ᵁ U.1),
        (w.left.ker.siteIdeal U).map (f₃.left.appLE U.1 U'.1 hU).hom ≤ I₃.siteIdeal U')
    (hg : x ≫ g = w) (e : f₁ ≫ f₂ ≫ f₃ = g) {yY : RationalPoint Y}
    (hI : I = yY.left.ker) (hy : yY ≫ f₂ ≫ f₃ = w) :
    (deformationSpecialFibreMap f₁ h₁ k' ≫ deformationSpecialFibreMap f₂ h₂ k') ≫
        deformationSpecialFibreMap f₃ h₃ k' =
      deformationSpecialFibreMap g (map_siteIdeal_ker_le_of_comp_eq g hg) k' := by
  subst hI
  rw [Category.assoc,
    deformationSpecialFibreMap_comp k' f₂ f₃ h₂ h₃ (map_siteIdeal_ker_le_of_comp_eq _ hy),
    deformationSpecialFibreMap_comp k' f₁ (f₂ ≫ f₃) h₁ _ (map_siteIdeal_ker_le_of_comp_eq _ (by
      rw [← hg, ← e]))]
  exact deformationSpecialFibreMap_eq_of_eq k' _ _ e _

@[reassoc (attr := simp)]
lemma deformationGenericMap_fst {f : X ⟶ Y}
    (hf : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
        J.siteIdeal U') :
    deformationGenericMap f hf k' ≫
        pullback.fst (deformationTotalToTrait Y I k') (traitGenericPoint k') =
      pullback.fst (deformationTotalToTrait X J k') (traitGenericPoint k') ≫
        deformationTotalMap f hf k' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationGenericMap_snd {f : X ⟶ Y}
    (hf : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
        J.siteIdeal U') :
    deformationGenericMap f hf k' ≫
        pullback.snd (deformationTotalToTrait Y I k') (traitGenericPoint k') =
      pullback.snd (deformationTotalToTrait X J k') (traitGenericPoint k') :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end TotalMap

section ProdLift

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
  {X Y C : Over (Spec (.of k))} {I : X.left.IdealSheafData} {J : Y.left.IdealSheafData}
  {K : C.left.IdealSheafData} (c₁ : C ⟶ X)
  (hJ₁ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₁.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (c₁.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')
  (c₂ : C ⟶ Y)
  (hJ₂ : ∀ ⦃U' : C.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ c₂.left ⁻¹ᵁ U.1), (J.siteIdeal U).map (c₂.left.appLE U.1 U'.1 hU).hom ≤
      K.siteIdeal U')

@[reassoc (attr := simp)]
lemma deformationProdLiftTotal_fst :
    deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂ ≫
        pullback.fst (deformationTotalToTrait X I k') (deformationTotalToTrait Y J k') =
      deformationTotalMap c₁ hJ₁ k' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationProdLiftTotal_snd :
    deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂ ≫
        pullback.snd (deformationTotalToTrait X I k') (deformationTotalToTrait Y J k') =
      deformationTotalMap c₂ hJ₂ k' :=
  pullback.lift_snd _ _ _

variable (X I) in
@[reassoc (attr := simp)]
lemma deformationDiagTotal_fst :
    deformationDiagTotal X I k' ≫
        pullback.fst (deformationTotalToTrait X I k') (deformationTotalToTrait X I k') = 𝟙 _ :=
  pullback.lift_fst _ _ _

variable (X I) in
@[reassoc (attr := simp)]
lemma deformationDiagTotal_snd :
    deformationDiagTotal X I k' ≫
        pullback.snd (deformationTotalToTrait X I k') (deformationTotalToTrait X I k') = 𝟙 _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma deformationProdLiftGeneric_fst :
    deformationProdLiftGeneric k' c₁ hJ₁ c₂ hJ₂ ≫
        pullback.fst (deformationProdTotalToTrait X I Y J k') (traitGenericPoint k') =
      pullback.fst (deformationTotalToTrait C K k') (traitGenericPoint k') ≫
        deformationProdLiftTotal k' c₁ hJ₁ c₂ hJ₂ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationProdLiftGeneric_snd :
    deformationProdLiftGeneric k' c₁ hJ₁ c₂ hJ₂ ≫
        pullback.snd (deformationProdTotalToTrait X I Y J k') (traitGenericPoint k') =
      pullback.snd (deformationTotalToTrait C K k') (traitGenericPoint k') :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

variable (X I) in
@[reassoc (attr := simp)]
lemma deformationDiagGeneric_fst :
    deformationDiagGeneric X I k' ≫
        pullback.fst (deformationProdTotalToTrait X I X I k') (traitGenericPoint k') =
      pullback.fst (deformationTotalToTrait X I k') (traitGenericPoint k') ≫
        deformationDiagTotal X I k' :=
  pullback.lift_fst _ _ _

variable (X I) in
@[reassoc (attr := simp)]
lemma deformationDiagGeneric_snd :
    deformationDiagGeneric X I k' ≫
        pullback.snd (deformationProdTotalToTrait X I X I k') (traitGenericPoint k') =
      pullback.snd (deformationTotalToTrait X I k') (traitGenericPoint k') :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end ProdLift

section ExchangeCongr

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}

/-- Two morphisms of models with the same morphisms of total spaces and of generic fibres, over
equal morphisms, have the same pushforward exchange (through the identifications of the
pushforwards along the equal morphisms). -/
lemma NearbyCyclesModel.Hom.pushforwardExchange_app_eq_of_eq {f₁ f₂ : X ⟶ Y} {f₁' f₂' : X' ⟶ Y'}
    (φ₁ : M.Hom N f₁ f₁') (φ₂ : M.Hom N f₂ f₂') (h : f₁ = f₂) (h' : f₁' = f₂')
    (htot : φ₁.total = φ₂.total) (hgen : φ₁.generic = φ₂.generic)
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (φ₁.pushforwardExchange Λ).app E ≫ eqToHom (by rw [h']) =
      (N.nearbyCycles Λ).map (eqToHom (by rw [h])) ≫ (φ₂.pushforwardExchange Λ).app E := by
  subst h h'
  obtain rfl : φ₁ = φ₂ := by
    cases φ₁
    cases φ₂
    congr
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end ExchangeCongr

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u)
  [Field k'] [Algebra k k'] {F : c.FixedLocus} {B : Over (Spec (.of k))} (j : B ⟶ F.F)
  {b : RationalPoint B} (hb : b ≫ j ≫ F.ι = y)

include hb in
lemma component_comp_d_eq : b ≫ j ≫ F.d = y ≫ c.c₁ := by
  rw [← F.ι_c₁, ← hb]
  simp only [Category.assoc]

/-- The morphism of deformation models `𝒟_B ⟶ 𝒳` over `d ∘ j : B ⟶ X`. -/
noncomputable abbrev componentPointModelHom :=
  pointComponentModelHom k' (j ≫ F.d) (component_comp_d_eq j hb)

/-- The composite morphism of models `𝒟_B ⟶ 𝒞 ⟶ 𝒞̄ ⟶ 𝒳 ×_S 𝒳` over `B ⊂ F ⊂ C ⊂ C̄ ⟶ X ⨯ X`. -/
noncomputable abbrev componentSupportModelHom :=
  ((componentModelHom k' j hb).comp (supportClosureOpenModelHom c y hc k')).comp
    (supportClosureProperModelHom c y k')

lemma componentSupportModelHom_total :
    (componentSupportModelHom hc k' j hb).total =
      (deformationTotalMap (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k' ≫
        deformationTotalMap (supportClosureι c) hc.map_siteIdeal_le_ker k') ≫
        deformationProdLiftTotal k' (supportClosureMap c ≫ prod.fst)
          (map_siteIdeal_le_closureLeg₁ c y) (supportClosureMap c ≫ prod.snd)
          (map_siteIdeal_le_closureLeg₂ c y) :=
  rfl

lemma componentSupportModelHom_total_fst :
    (componentSupportModelHom hc k' j hb).total ≫ pullback.fst _ _ =
      (componentPointModelHom k' j hb).total := by
  rw [componentSupportModelHom_total, Category.assoc, deformationProdLiftTotal_fst]
  exact deformationTotalMap_comp_comp_of_eq k' _ _ _ _ _ _ _ (component_comp_d_eq j hb)
    (by simp [← F.ι_c₁, supportClosureι_map_assoc]) rfl
    (by simp [supportClosureι_map_assoc])


lemma componentSupportModelHom_total_snd :
    (componentSupportModelHom hc k' j hb).total ≫ pullback.snd _ _ =
      (componentPointModelHom k' j hb).total := by
  rw [componentSupportModelHom_total, Category.assoc, deformationProdLiftTotal_snd]
  exact deformationTotalMap_comp_comp_of_eq k' _ _ _ _ _ _ _ (component_comp_d_eq j hb)
    (by simp [← F.ι_c₂, supportClosureι_map_assoc]) rfl
    (by simp [supportClosureι_map_assoc, hc.comp_c₁_eq_comp_c₂])

/-- The two morphisms of models `𝒟_B ⟶ 𝒳 ×_S 𝒳` have the same morphism of total spaces. -/
lemma componentPointModelHom_total_comp_diag :
    (componentPointModelHom k' j hb).total ≫ deformationDiagTotal X (y ≫ c.c₁).left.ker k' =
      (componentSupportModelHom hc k' j hb).total := by
  apply pullback.hom_ext
  · rw [Category.assoc, deformationDiagTotal_fst]
    exact (Category.comp_id _).trans (componentSupportModelHom_total_fst hc k' j hb).symm
  · rw [Category.assoc, deformationDiagTotal_snd]
    exact (Category.comp_id _).trans (componentSupportModelHom_total_snd hc k' j hb).symm


lemma componentSupportModelHom_generic :
    (componentSupportModelHom hc k' j hb).generic =
      (deformationGenericMap (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k' ≫
        deformationGenericMap (supportClosureι c) hc.map_siteIdeal_le_ker k') ≫
        deformationProdLiftGeneric k' (supportClosureMap c ≫ prod.fst)
          (map_siteIdeal_le_closureLeg₁ c y) (supportClosureMap c ≫ prod.snd)
          (map_siteIdeal_le_closureLeg₂ c y) :=
  rfl

/-- The two morphisms of models `𝒟_B ⟶ 𝒳 ×_S 𝒳` have the same morphism of generic fibres. -/
lemma componentPointModelHom_generic_comp_diag :
    (componentPointModelHom k' j hb).generic ≫ deformationDiagGeneric X (y ≫ c.c₁).left.ker k' =
      (componentSupportModelHom hc k' j hb).generic := by
  rw [componentSupportModelHom_generic]
  apply pullback.hom_ext
  · rw [Category.assoc, deformationDiagGeneric_fst, Category.assoc, Category.assoc,
      deformationProdLiftGeneric_fst, deformationGenericMap_fst_assoc,
      deformationGenericMap_fst_assoc]
    have h := componentPointModelHom_total_comp_diag hc k' j hb
    rw [componentSupportModelHom_total] at h
    simp only [Category.assoc] at h
    rw [← h]
    exact deformationGenericMap_fst_assoc _ _ _
  · rw [Category.assoc, deformationDiagGeneric_snd, Category.assoc, Category.assoc,
      deformationProdLiftGeneric_snd, deformationGenericMap_snd, deformationGenericMap_snd]
    exact deformationGenericMap_snd _ _


lemma componentPointModelHom_comp_diag_left :
    (j ≫ F.d).left ≫ (diag X).left =
      ((j ≫ F.ι).left ≫ (supportClosureι c).left) ≫
        (prod.lift (supportClosureMap c ≫ prod.fst) (supportClosureMap c ≫ prod.snd)).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, prodLift_supportClosureMap]
  congr 1
  rw [Category.assoc, Category.assoc, supportClosureι_map, Category.assoc, F.ι_support]

lemma componentPointModelHom_comp_diag_special :
    (deformationSpecialFibreMap (j ≫ F.d)
      (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb))
        k').left ≫ (diag (deformationSpecialFibre X (y ≫ c.c₁).left.ker k')).left =
      ((componentSpecialFibreMap k' j hb).left ≫
        (deformationSpecialFibreMap (supportClosureι c) hc.map_siteIdeal_le_ker k').left) ≫
        (prod.lift
          (deformationSpecialFibreMap (supportClosureMap c ≫ prod.fst)
            (map_siteIdeal_le_closureLeg₁ c y) k')
          (deformationSpecialFibreMap (supportClosureMap c ≫ prod.snd)
            (map_siteIdeal_le_closureLeg₂ c y) k')).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
  congr 1
  apply prod.hom_ext
  · rw [Category.assoc, diag, prod.lift_fst, Category.comp_id, Category.assoc, prod.lift_fst]
    exact (deformationSpecialFibreMap_comp_comp_of_eq k' _ _ _ _ _ _ _ (component_comp_d_eq j hb)
      (by simp [← F.ι_c₁, supportClosureι_map_assoc]) rfl
      (by simp [supportClosureι_map_assoc])).symm
  · rw [Category.assoc, diag, prod.lift_snd, Category.comp_id, Category.assoc, prod.lift_snd]
    exact (deformationSpecialFibreMap_comp_comp_of_eq k' _ _ _ _ _ _ _ (component_comp_d_eq j hb)
      (by simp [← F.ι_c₂, supportClosureι_map_assoc]) rfl
      (by simp [supportClosureι_map_assoc, hc.comp_c₁_eq_comp_c₂])).symm

/-- **Composition law for the support on a component**: the pushforward exchange of
`𝒟_B ⟶ 𝒞 ⟶ 𝒞̄ ⟶ 𝒳 ×_S 𝒳` is that of `𝒟_B ⟶ 𝒳` (over `d ∘ j`) followed by that of the
diagonal, through the composition isomorphisms. -/
theorem componentSupportModelHom_pushforwardExchange_app
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) B.left))) :
    type_of% (NearbyCyclesModel.Hom.pushforwardExchange_comp_app_of_eq
      (Profinite.padicAlgClRingObj ℓ) (componentPointModelHom k' j hb)
      (deformationDiagModelHom X (y ≫ c.c₁).left.ker k') (componentSupportModelHom hc k' j hb)
      (componentPointModelHom_comp_diag_left (F := F) j)
      (componentPointModelHom_comp_diag_special hc k' j hb)
      (componentPointModelHom_total_comp_diag hc k' j hb)
      (componentPointModelHom_generic_comp_diag hc k' j hb) E) :=
  NearbyCyclesModel.Hom.pushforwardExchange_comp_app_of_eq
    (Profinite.padicAlgClRingObj ℓ) (componentPointModelHom k' j hb)
    (deformationDiagModelHom X (y ≫ c.c₁).left.ker k') (componentSupportModelHom hc k' j hb)
    (componentPointModelHom_comp_diag_left (F := F) j)
    (componentPointModelHom_comp_diag_special hc k' j hb)
    (componentPointModelHom_total_comp_diag hc k' j hb)
    (componentPointModelHom_generic_comp_diag hc k' j hb) E



section ToPoint

/-- The composite morphism of models `𝒟_B ⟶ 𝒳 ⟶ 𝒳̄ ⟶ 𝒫 ⟶ S` of the exchange `ν_X` on
pushforwards from `B` (`pointCompactSupportExchangeOfSeparated_app_lowerStar_component_eq`). -/
noncomputable abbrev componentToPointModelHom :=
  pointCompModelHom (y ≫ c.c₁) (compactificationOverField (toPoint X)).overI k'
    (componentPointModelHom k' j hb)

lemma componentToPointModelHom_total :
    (componentToPointModelHom k' j hb).total =
      ((deformationTotalMap (j ≫ F.d) 
          (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb)) k' ≫
        deformationTotalMap (compactificationOverField (toPoint X)).overI
          (ker_compatible_of_isOpenImmersion _ _) k') ≫
        deformationTotalToCompactified (compactificationOverField (toPoint X)).overObj
          ((y ≫ c.c₁) ≫ (compactificationOverField (toPoint X)).overI) k') ≫
        compactifiedTotalToTrait (compactificationOverField (toPoint X)).overObj
          ((y ≫ c.c₁) ≫ (compactificationOverField (toPoint X)).overI) k' :=
  rfl

/-- The composite `𝒟_B ⟶ S` of `componentToPointModelHom` is the structure map of the deformation
of `B` (the total morphism of `deformationToTraitModelHom`). -/
lemma componentToPointModelHom_total_eq :
    (componentToPointModelHom k' j hb).total = deformationTotalToTrait B b.left.ker k' := by
  rw [componentToPointModelHom_total, Category.assoc, deformationTotalToCompactified_toTrait,
    Category.assoc, deformationTotalMap_toTrait, deformationTotalMap_toTrait]

lemma componentToPointModelHom_generic :
    (componentToPointModelHom k' j hb).generic =
      ((deformationGenericMap (j ≫ F.d) 
          (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb)) k' ≫
        deformationGenericMap (compactificationOverField (toPoint X)).overI
          (ker_compatible_of_isOpenImmersion _ _) k') ≫
        deformationGenericToCompactified (compactificationOverField (toPoint X)).overObj
          ((y ≫ c.c₁) ≫ (compactificationOverField (toPoint X)).overI) k') ≫
        compactifiedGenericToPoint (compactificationOverField (toPoint X)).overObj
          ((y ≫ c.c₁) ≫ (compactificationOverField (toPoint X)).overI) k' :=
  rfl

/-- The composite `𝒟_{B,Ω} ⟶ Spec Ω` of `componentToPointModelHom` is the projection (the generic
morphism of `deformationToTraitModelHom`). -/
lemma componentToPointModelHom_generic_eq :
    (componentToPointModelHom k' j hb).generic =
      pullback.snd (deformationTotalToTrait B b.left.ker k') (traitGenericPoint k') := by
  rw [componentToPointModelHom_generic, Category.assoc, deformationGenericToCompactified_toPoint,
    Category.assoc, deformationGenericMap_snd, deformationGenericMap_snd]


lemma componentToPointModelHom_left :
    ((((j ≫ F.d).left ≫ (compactificationOverField (toPoint X)).overI.left) ≫
        𝟙 (compactificationOverField (toPoint X)).overObj.left) ≫
        (toPoint (compactificationOverField (toPoint X)).overObj).left) = (toPoint B).left := by
  rw [Category.comp_id, ← Over.comp_left, ← Over.comp_left, comp_toPoint]

lemma componentToPointModelHom_special :
    (((deformationSpecialFibreMap (j ≫ F.d)
      (map_siteIdeal_ker_le_of_comp_eq _ (component_comp_d_eq j hb))
        k').left ≫
        (pointSpecialMap (y ≫ c.c₁) (compactificationOverField (toPoint X)).overI k').left) ≫
        (deformationSpecialFibreToCompactified (compactificationOverField (toPoint X)).overObj
          ((y ≫ c.c₁) ≫ (compactificationOverField (toPoint X)).overI) k').left) ≫
        (toPoint (compactifiedSpecialFibre (compactificationOverField (toPoint X)).overObj
          ((y ≫ c.c₁) ≫ (compactificationOverField (toPoint X)).overI) k')).left =
      (toPoint (deformationSpecialFibre B b.left.ker k')).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_toPoint]

/-- **The composite exchange of `ν_X` on `B` is that of the deformation of `B`**: the pushforward
exchange of `componentToPointModelHom` is that of `deformationToTraitModelHom` (whose inverse is
`deformationCompactSupportExchange`), through the identifications of the pushforwards along the
equal structure maps. -/
theorem componentToPointModelHom_pushforwardExchange_app
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) B.left))) :
    type_of% (NearbyCyclesModel.Hom.pushforwardExchange_app_eq_of_eq
      (Profinite.padicAlgClRingObj ℓ) (componentToPointModelHom k' j hb)
      (deformationToTraitModelHom B b.left.ker k') (componentToPointModelHom_left (F := F) j)
      (componentToPointModelHom_special k' j hb) (componentToPointModelHom_total_eq k' j hb)
      (componentToPointModelHom_generic_eq k' j hb) E) :=
  NearbyCyclesModel.Hom.pushforwardExchange_app_eq_of_eq
    (Profinite.padicAlgClRingObj ℓ) (componentToPointModelHom k' j hb)
    (deformationToTraitModelHom B b.left.ker k') (componentToPointModelHom_left (F := F) j)
    (componentToPointModelHom_special k' j hb) (componentToPointModelHom_total_eq k' j hb)
    (componentToPointModelHom_generic_eq k' j hb) E

end ToPoint

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
