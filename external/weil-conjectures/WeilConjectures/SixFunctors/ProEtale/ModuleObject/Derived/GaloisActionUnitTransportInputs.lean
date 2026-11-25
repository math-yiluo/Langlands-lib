/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisActionUnitTransport

/-!
# Inputs of the identification of the unit transport with the Galois action

This file discharges the homotopy-category input of
`ProEtale.CondensedRing.derivedUnitTransport_eq_derivedGaloisAction_app` and reduces the
underived input to an identity after the counit.

## Main results

- `CategoryTheory.unitTransport_mapHomotopyCategory_quotient` and
  `ProEtale.CondensedRing.unitTransportHomotopyCompatible`: the unit transport on homotopy
  categories is the unit transport of module objects applied levelwise, i.e.
  `ProEtale.CondensedRing.UnitTransportHomotopyCompatible` holds.
- `CategoryTheory.unitTransport_app_eq_unit_comp`, `ProEtale.CondensedRing.unitTransport_app_eq`:
  the unit transport is the transpose of `c ≫ s^*(ε_g) ≫ c⁻¹`.
- `ProEtale.CondensedRing.galoisAction_eq_unitTransport_of_counit`: the Galois action is the unit
  transport as soon as both agree after `g^*` and the counit.
- `exists_retraction_pullbackExchange_galoisLayerHom_of_galoisAction_eq`:
  the splitting of the pullback exchange of a finite Galois layer, assuming only the underived
  identification of the Galois actions with the unit transports.

## Implementation notes

The underived identification `galoisAction Λ g hρ a = unitTransport Λ (ρ σ) (hρ σ) (hρ σ)` is
not proved here. By `ProEtale.CondensedRing.galoisAction_eq_unitTransport_of_counit` it reduces
to `g^*(ρ_a) ≫ ε = c ≫ (ρ σ)^*(ε) ≫ c⁻¹` on `g^* g_* g^* M`; this requires comparing the module
pullbacks with the abelian ones (through the extension of scalars along `α_g`) and the abelian
ones with the restrictions along the localization functors.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

section QuotientApp

variable {ι V W W' : Type*} {c : ComplexShape ι} [Category V] [Category W] [Category W']
  [Preadditive V] [Preadditive W] [Preadditive W']

/-- `Functor.mapHomotopyCategoryCompIso` on the image of a complex. -/
lemma Functor.mapHomotopyCategoryCompIso_hom_app_quotient {F : V ⥤ W} {G : W ⥤ W'}
    {H : V ⥤ W'} (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive]
    (M : HomologicalComplex V c) :
    (Functor.mapHomotopyCategoryCompIso e c).hom.app ((HomotopyCategory.quotient V c).obj M) =
      (HomotopyCategory.quotient W' c).map ((Functor.mapHomologicalComplexCompIso e c).hom.app M) :=
  rfl

/-- `Functor.mapHomotopyCategoryCompIso` on the image of a complex. -/
lemma Functor.mapHomotopyCategoryCompIso_inv_app_quotient {F : V ⥤ W} {G : W ⥤ W'}
    {H : V ⥤ W'} (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive]
    (M : HomologicalComplex V c) :
    (Functor.mapHomotopyCategoryCompIso e c).inv.app ((HomotopyCategory.quotient V c).obj M) =
      (HomotopyCategory.quotient W' c).map ((Functor.mapHomologicalComplexCompIso e c).inv.app M) :=
  rfl

/-- `NatTrans.mapHomotopyCategory` on the image of a complex. -/
lemma NatTrans.mapHomotopyCategory_app_quotient {F G : V ⥤ W} [F.Additive] [G.Additive]
    (τ : F ⟶ G) (M : HomologicalComplex V c) :
    (NatTrans.mapHomotopyCategory τ c).app ((HomotopyCategory.quotient V c).obj M) =
      (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex τ c).app M) :=
  rfl

end QuotientApp

variable {ι : Type*} {c : ComplexShape ι} {A B B' : Type*} [Category A] [Category B]
  [Category B'] [Preadditive A] [Preadditive B] [Preadditive B']
  [(HomotopyCategory.quotient A c).IsLocalization (HomologicalComplex.homotopyEquivalences A c)]
  [(HomotopyCategory.quotient B c).IsLocalization (HomologicalComplex.homotopyEquivalences B c)]
  [(HomotopyCategory.quotient B' c).IsLocalization
    (HomologicalComplex.homotopyEquivalences B' c)]

/-- **The unit transport on homotopy categories** of the image of a complex, built from the
induced adjunctions and composition isomorphism, is the unit transport of the underlying
adjunctions applied levelwise. -/
lemma unitTransport_mapHomotopyCategory_quotient {Gg : A ⥤ B} {Fg : B ⥤ A} {Gs : B ⥤ B'}
    {Fs : B' ⥤ B} {Gsg : A ⥤ B'} {Fsg : B' ⥤ A}
    (ag : Gg ⊣ Fg) (as : Gs ⊣ Fs) (asg : Gsg ⊣ Fsg) [Gg.Additive] [Fg.Additive] [Gs.Additive]
    [Fs.Additive] [Gsg.Additive] [Fsg.Additive] (e : Gsg ≅ Gg ⋙ Gs)
    (L : HomologicalComplex A c) :
    (Fg.mapHomotopyCategory c).map ((as.mapHomotopyCategory c).unit.app
        ((Gg.mapHomotopyCategory c).obj ((HomotopyCategory.quotient A c).obj L))) ≫
      (conjugateEquiv ((ag.mapHomotopyCategory c).comp (as.mapHomotopyCategory c))
        (asg.mapHomotopyCategory c) (Functor.mapHomotopyCategoryCompIso e.symm c).symm.hom).app
          ((Gs.mapHomotopyCategory c).obj
            ((Gg.mapHomotopyCategory c).obj ((HomotopyCategory.quotient A c).obj L))) ≫
      (Fsg.mapHomotopyCategory c).map
        ((Functor.mapHomotopyCategoryCompIso e.symm c).symm.inv.app
          ((HomotopyCategory.quotient A c).obj L)) =
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (Gg ⋙ Fg)) c).hom.app
        ((HomotopyCategory.quotient A c).obj L) ≫
      (NatTrans.mapHomotopyCategory (Functor.whiskerLeft Gg (Functor.whiskerRight as.unit Fg) ≫
        Functor.whiskerLeft (Gg ⋙ Gs) (conjugateEquiv (ag.comp as) asg e.hom) ≫
        Functor.whiskerRight e.inv Fsg) c).app ((HomotopyCategory.quotient A c).obj L) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (Gsg ⋙ Fsg)) c).inv.app
        ((HomotopyCategory.quotient A c).obj L) := by
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app, Functor.map_comp,
    Category.assoc]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient (c := c) as
      ((Gg.mapHomologicalComplex c).obj L),
    Adjunction.mapHomotopyCategory_unit_app_quotient (c := c) asg
      ((Fg.mapHomologicalComplex c).obj ((Fs.mapHomologicalComplex c).obj
        ((Gs.mapHomologicalComplex c).obj ((Gg.mapHomologicalComplex c).obj L)))),
    Adjunction.mapHomotopyCategory_counit_app_quotient (c := c) ag
      ((Fs.mapHomologicalComplex c).obj
        ((Gs.mapHomologicalComplex c).obj ((Gg.mapHomologicalComplex c).obj L))),
    Adjunction.mapHomotopyCategory_counit_app_quotient (c := c) as
      ((Gs.mapHomologicalComplex c).obj ((Gg.mapHomologicalComplex c).obj L))]
  simp only [Iso.symm_hom, Iso.symm_inv]
  erw [Functor.mapHomotopyCategoryCompIso_inv_app_quotient (c := c) e.symm
      ((Fg.mapHomologicalComplex c).obj ((Fs.mapHomologicalComplex c).obj
        ((Gs.mapHomologicalComplex c).obj ((Gg.mapHomologicalComplex c).obj L))))]
  simp only [Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategoryCompIso_hom_app_quotient,
    Functor.mapHomotopyCategoryCompIso_inv_app_quotient, NatTrans.mapHomotopyCategory_app_quotient,
    ← Functor.map_comp]
  congr 1
  ext n
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.symm_inv,
    Adjunction.mapHomologicalComplex_counit_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Iso.symm_hom, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app, Category.assoc,
    Iso.refl_hom, NatTrans.id_app, NatTrans.mapHomologicalComplex_app_f, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, conjugateEquiv_apply_app, Adjunction.comp_counit_app, Iso.refl_inv]
  erw [Category.id_comp, Category.comp_id]
  rfl

/-- **The unit transport through the adjunction**: the unit transport along `s` of `Fg Gg` is
the transpose, under `Gsg ⊣ Fsg`, of `c ≫ Gs(ε_g) ≫ c⁻¹ : Gsg Fg Gg ⟶ Gsg`; it involves the
pullbacks only through the composition isomorphism `c`. -/
lemma unitTransport_app_eq_unit_comp {C_X C_Y C_Y' : Type*} [Category C_X] [Category C_Y]
    [Category C_Y'] {Gg : C_X ⥤ C_Y} {Fg : C_Y ⥤ C_X} {Gs : C_Y ⥤ C_Y'} {Fs : C_Y' ⥤ C_Y}
    {Gsg : C_X ⥤ C_Y'} {Fsg : C_Y' ⥤ C_X} (ag : Gg ⊣ Fg) (as : Gs ⊣ Fs) (asg : Gsg ⊣ Fsg)
    (c : Gsg ≅ Gg ⋙ Gs) (M : C_X) :
    Fg.map (as.unit.app (Gg.obj M)) ≫
        (conjugateEquiv (ag.comp as) asg c.hom).app (Gs.obj (Gg.obj M)) ≫
        Fsg.map (c.inv.app M) =
      asg.unit.app (Fg.obj (Gg.obj M)) ≫ Fsg.map (c.hom.app (Fg.obj (Gg.obj M)) ≫
        Gs.map (ag.counit.app (Gg.obj M)) ≫ c.inv.app M) := by
  have h₁ := asg.unit.naturality (Fg.map (as.unit.app (Gg.obj M)))
  have h₂ := c.hom.naturality (Fg.map (as.unit.app (Gg.obj M)))
  have h₃ := ag.counit.naturality (as.unit.app (Gg.obj M))
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h₁ h₂ h₃
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁]
  simp only [← Functor.map_comp]
  refine congrArg (fun x ↦ asg.unit.app (Fg.obj (Gg.obj M)) ≫ Fsg.map x) ?_
  rw [reassoc_of% h₂, ← Gs.map_comp_assoc, h₃, Gs.map_comp_assoc,
    as.left_triangle_components_assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Obj CategoryTheory.Functor

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The composition isomorphism of pushforwards of module objects is the conjugate of that of
pullbacks. -/
lemma lowerStarComp_hom_eq_conjugateEquiv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lowerStarComp Λ f g).hom = conjugateEquiv
      ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
      (upperStarLowerStarAdjunction Λ (f ≫ g)) (upperStarComp Λ f g).hom := by
  have h := congrArg Iso.inv ((conjugateIsoEquiv (upperStarLowerStarAdjunction Λ (f ≫ g))
    ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))).apply_symm_apply
      (lowerStarComp Λ f g).symm)
  exact h.symm

/-- **`ProEtale.CondensedRing.UnitTransportHomotopyCompatible` holds**: the unit transport on
homotopy categories is the unit transport of module objects applied levelwise. -/
theorem unitTransportHomotopyCompatible {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X) :
    UnitTransportHomotopyCompatible Λ s g := by
  intro K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [unitTransport, lowerStarComp_hom_eq_conjugateEquiv, eqToHom_refl, Category.comp_id]
  exact unitTransport_mapHomotopyCategory_quotient (upperStarLowerStarAdjunction Λ g)
    (upperStarLowerStarAdjunction Λ s) (upperStarLowerStarAdjunction Λ (s ≫ g))
    (upperStarComp Λ s g) L

/-- **The unit transport of module objects through the adjunction** `p₁^* ⊣ p₁_*`: it is the
transpose of `c ≫ s^*(ε_g) ≫ c⁻¹ : p₁^* g_* g^* M ⟶ p₁^* M` for the composition isomorphism
`c : p₁^* ≅ g^* ⋙ s^*`. -/
lemma unitTransport_app_eq {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X) {p₁ : Y' ⟶ X}
    (hp : s ≫ g = p₁)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (unitTransport Λ s hp hp).app M =
      (upperStarLowerStarAdjunction Λ p₁).unit.app ((g)_*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) ≫
        (p₁)_*⟦Λ⟧.map ((upperStarCongr Λ hp.symm ≪≫ upperStarComp Λ s g).hom.app
            ((g)_*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) ≫
          (s)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ g).counit.app ((g)^*⟦Λ⟧.obj M)) ≫
          (upperStarCongr Λ hp.symm ≪≫ upperStarComp Λ s g).inv.app M) := by
  subst hp
  simp only [unitTransport, upperStarCongr_self, Iso.refl_trans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, eqToHom_refl,
    Category.comp_id, lowerStarComp_hom_eq_conjugateEquiv]
  exact unitTransport_app_eq_unit_comp (upperStarLowerStarAdjunction Λ g)
    (upperStarLowerStarAdjunction Λ s) (upperStarLowerStarAdjunction Λ (s ≫ g))
    (upperStarComp Λ s g) M

/-- **Reduction of the underived identification to the counit**: the Galois action of `a` on
`g_* g^*` is the unit transport along `ρ σ` as soon as, after `g^*` and the counit, it becomes
`c ≫ (ρ σ)^*(ε_g) ≫ c⁻¹` for the composition isomorphism `c : g^* ≅ g^* ⋙ (ρ σ)^*` (transported
along `ρ σ ≫ g = g`). -/
theorem galoisAction_eq_unitTransport_of_counit {X Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g]
    [Etale g] [Surjective g] {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g) (σ a : Γ)
    (h : ∀ M, (g)^*⟦Λ⟧.map ((galoisAction Λ g hρ a).app M) ≫
        (upperStarLowerStarAdjunction Λ g).counit.app ((g)^*⟦Λ⟧.obj M) =
      (upperStarCongr Λ (hρ σ).symm ≪≫ upperStarComp Λ (ρ σ) g).hom.app
          ((g)_*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) ≫
        (ρ σ)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ g).counit.app ((g)^*⟦Λ⟧.obj M)) ≫
        (upperStarCongr Λ (hρ σ).symm ≪≫ upperStarComp Λ (ρ σ) g).inv.app M) :
    galoisAction Λ g hρ a = unitTransport Λ (ρ σ) (hρ σ) (hρ σ) := by
  ext M : 2
  rw [unitTransport_app_eq, ← h M, Functor.map_comp]
  have hn := (upperStarLowerStarAdjunction Λ g).unit.naturality_assoc
    ((galoisAction Λ g hρ a).app M)
    ((g)_*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ g).counit.app ((g)^*⟦Λ⟧.obj M)))
  simp only [Functor.id_map, Functor.comp_map] at hn
  erw [← hn, Adjunction.right_triangle_components, Category.comp_id]

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (L' : Type u) [Field L'] [Algebra L L']
  [FiniteDimensional L L'] [IsGalois L L']

/-- The automorphisms `ρ_σ` of the generic fibre of a finite Galois layer are isomorphisms. -/
instance isIso_pullbackAction (σ : L' ≃ₐ[L] L') :
    IsIso (pullbackAction h _ specGaloisAction_comp σ) := by
  have h1 : specGaloisAction L L' 1 = 𝟙 _ := by
    rw [specGaloisAction, ← Spec.map_id]
    rfl
  refine ⟨pullbackAction h _ specGaloisAction_comp σ⁻¹, ?_, ?_⟩
  · rw [pullbackAction_mul h _ specGaloisAction_comp specGaloisAction_mul]
    ext <;> simp [h1]
  · rw [pullbackAction_mul h _ specGaloisAction_comp specGaloisAction_mul]
    ext <;> simp [h1]

-- the derived functors and their composition isomorphisms are large terms
/-- **The pullback exchange of a finite Galois layer is split by the averaged action on nearby
cycles**, given only the underived identification of the Galois actions `galoisAction (e σ)`
on `g_* g^*` (for the projection `g` of the generic fibre) with the unit transports along
`ρ_σ`: the derived identification `hact` of
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom'` follows. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_of_galoisAction_eq
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso (Fintype.card (L' ≃ₐ[L] L') • 𝟙 (L((N.ε)^*⟦Λ⟧).obj C))]
    (e : (L' ≃ₐ[L] L') ≃ (L' ≃ₐ[L] L'))
    (hgal : ∀ σ, galoisAction Λ (pullback.fst _ _)
      (pullbackAction_fst h _ specGaloisAction_comp) (e σ) =
        unitTransport Λ (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)) :
    ∃ r, ((N.galoisLayerHom h L').pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      Fintype.card (L' ≃ₐ[L] L') • (r ≫ ((N.galoisLayerHom h L').pullbackExchange Λ).app C) =
        ∑ σ, (N.galoisLayerAut h L' σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) :=
  exists_retraction_pullbackExchange_galoisLayerHom' Λ N h L' C e fun σ ↦
    derivedUnitTransport_eq_derivedGaloisAction_app Λ _ _ σ (e σ)
      (unitTransportHomotopyCompatible Λ _ _) (hgal σ) _

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
