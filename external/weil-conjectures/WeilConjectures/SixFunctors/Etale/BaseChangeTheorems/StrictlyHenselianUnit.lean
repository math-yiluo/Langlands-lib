/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf

/-!
# The unit of `t^* ⊣ Rt_*` at a constant sheaf over a strictly henselian local ring

Let `R` be a strictly henselian local ring, `Y = Spec R`, `s₀ : Spec κ ⟶ Y` the closed point
(`κ` the residue field, which is separably closed) and `t : Spec Ω ⟶ Y` any morphism from the
spectrum of a separably closed field. For every `Λ`-module `M`, the pullback along `s₀` of the
unit `M_Y ⟶ Rt_* t^* M_Y` of the derived adjunction `t^* ⊣ Rt_*` at the constant sheaf `M_Y`
is an isomorphism in `D⁺(Spec κ)`
(`AlgebraicGeometry.Etale.isIso_upperStar_map_unit_constantSheaf_of_isStrictlyHenselianLocalRing`).

We check this on homology sheaves. A sheaf on `Spec κ` is determined by its global sections, and
the global sections of `s₀^* G` are those of `G` over `Y`
(`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing`). Over the strictly
henselian `Y`, the sections over `Y` of a sheafification are those of the presheaf. Hence:

* in degree `q ≠ 0`, the sections over `Y` of `R^q t_* (t^* M_Y)` are
  `Hom(t^* Λ[Y][0], (t^* M_Y)[0][q]) = 0`, since `t^* Λ[Y]` is a constant sheaf on the
  separably closed point `Spec Ω`, hence projective;
* in degree `0`, the sections over `Y` of `H⁰` of an object `L` are `Hom(Λ[Y][0], L)`, and the
  map induced by the unit is `t^* : Hom(Λ[Y], M_Y) ⟶ Hom(t^* Λ[Y], t^* M_Y)`, which is bijective
  since the constant sheaf functors on `Y` and on `Spec Ω` are fully faithful.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

/-- A morphism of presheaves which is locally injective and locally surjective is bijective on
sections over an object `U` all of whose covering sieves contain the identity. -/
lemma CategoryTheory.Presheaf.bijective_app_of_forall_id_mem {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A : Type*} [Category* A] {FA : A → A → Type*}
    {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) [Presheaf.IsLocallyInjective J φ]
    [Presheaf.IsLocallySurjective J φ] (U : C) (hU : ∀ S ∈ J U, S.arrows (𝟙 U)) :
    Function.Bijective (φ.app (op U)) := by
  refine ⟨fun x y h ↦ ?_, fun s ↦ ?_⟩
  · simpa using hU _ (Presheaf.equalizerSieve_mem J φ x y h)
  · obtain ⟨t, ht⟩ := hU _ (Presheaf.imageSieve_mem J φ s)
    exact ⟨t, ht.trans (by simp)⟩

/-- Let `S` and `S'` be fully faithful functors and `e : S ⋙ F ≅ F' ⋙ S'`. If `F'` is bijective
on morphisms `X ⟶ Y`, then `F` is bijective on morphisms `S X ⟶ S Y`. -/
lemma CategoryTheory.Functor.bijective_map_of_fullyFaithful_of_iso {C D C' D' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D'] {S : C ⥤ D} {S' : C' ⥤ D'}
    (hS : S.FullyFaithful) (hS' : S'.FullyFaithful) {F' : C ⥤ C'} {F : D ⥤ D'}
    (e : S ⋙ F ≅ F' ⋙ S') {X Y : C} (h : Function.Bijective (F'.map : (X ⟶ Y) → _)) :
    Function.Bijective (F.map : (S.obj X ⟶ S.obj Y) → _) := by
  have key : (F.map : (S.obj X ⟶ S.obj Y) → _) ∘ S.map =
      ((e.app X).symm.homCongr (e.app Y).symm) ∘ S'.map ∘ F'.map := by
    funext f
    have hn := e.hom.naturality f
    simp only [Functor.comp_map] at hn
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.app_hom, Iso.symm_hom,
      Iso.app_inv]
    rw [← reassoc_of% hn, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [← Function.Bijective.of_comp_iff _ (hS.map_bijective X Y), key]
  exact (Equiv.bijective _).comp ((hS'.map_bijective _ _).comp h)

/-- A functor is bijective on morphisms `X ⟶ Y` as soon as it is bijective on morphisms
`X' ⟶ Y` for some `X' ≅ X`. -/
lemma CategoryTheory.Functor.bijective_map_of_iso_left {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) {X X' Y : C} (i : X ≅ X')
    (h : Function.Bijective (F.map : (X' ⟶ Y) → _)) :
    Function.Bijective (F.map : (X ⟶ Y) → _) := by
  have key : (F.map : (X ⟶ Y) → _) =
      (fun g ↦ F.map i.hom ≫ g) ∘ (F.map : (X' ⟶ Y) → _) ∘ (fun f ↦ i.inv ≫ f) := by
    funext f
    simp
  rw [key]
  refine (Function.bijective_iff_has_inverse.2 ⟨fun g ↦ F.map i.inv ≫ g, fun g ↦ ?_,
    fun g ↦ ?_⟩).comp (h.comp (Function.bijective_iff_has_inverse.2 ⟨fun g ↦ i.hom ≫ g,
      fun g ↦ ?_, fun g ↦ ?_⟩)) <;> simp [← Functor.map_comp_assoc]

/-- In the bounded below derived category, there are no nonzero morphisms from a projective
object placed in degree `0` to the shift by `q ≠ 0` of an object placed in degree `0`. -/
lemma DerivedCategory.Plus.subsingleton_hom_shift_of_projective {C : Type*} [Category* C]
    [Abelian C] [HasDerivedCategory C] (P N : C) [Projective P] {q : ℤ} (hq : q ≠ 0) :
    Subsingleton ((singleFunctor C 0).obj P ⟶ ((singleFunctor C 0).obj N)⟦q⟧) := by
  suffices h : ∀ f : (singleFunctor C 0).obj P ⟶ ((singleFunctor C 0).obj N)⟦q⟧, f = 0 from
    ⟨fun f g ↦ (h f).trans (h g).symm⟩
  intro f
  apply Plus.ι.map_injective
  let e : Plus.ι.obj (((singleFunctor C 0).obj N)⟦q⟧) ≅
      (DerivedCategory.singleFunctor C (-q)).obj N :=
    (Plus.ι.commShiftIso q).app _ ≪≫
      ((DerivedCategory.singleFunctors C).shiftIso q (-q) 0 (by lia)).app N
  let g : (DerivedCategory.singleFunctor C 0).obj P ⟶
      (DerivedCategory.singleFunctor C (-q)).obj N :=
    (singleFunctorιIso C 0).inv.app P ≫ Plus.ι.map f ≫ e.hom
  have hg : g = 0 := by
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g 0 (-q) (by lia)
        inferInstance inferInstance
    · rw [← cancel_epi ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app P),
        ← cancel_mono ((DerivedCategory.singleFunctorIsoCompQ C (-q)).hom.app N),
        comp_zero, zero_comp]
      exact from_singleFunctor_obj_eq_zero_of_projective _ (-q) (by lia)
  rw [Functor.map_zero, ← cancel_mono e.hom, zero_comp,
    ← cancel_epi ((singleFunctorιIso C 0).inv.app P), comp_zero]
  exact hg

namespace AlgebraicGeometry

open Scheme Etale

section GlobalSections

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback map on global sections `Γ(Y, G) ⟶ Γ(X, f^* G)` is natural in `G`. -/
lemma Etale.globalSectionsUpperStarMap_naturality {X Y : Scheme.{u}} (m : X ⟶ Y)
    {F F' : Sheaf Y.smallEtaleTopology A} (k : F ⟶ F') :
    (Sheaf.Γ Y.smallEtaleTopology A).map k ≫ globalSectionsUpperStarMap A m F' =
    globalSectionsUpperStarMap A m F ≫
      (Sheaf.Γ X.smallEtaleTopology A).map ((upperStar A m).map k) := by
  let eL := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A terminalIsTerminal
  let eK := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A terminalIsTerminal
  let adj := upperStarLowerStarAdjunction A m
  have hu := congrArg (fun φ ↦ φ.hom.app (op (⊤_ Y.Etale))) (adj.unit.naturality k)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  simp only [globalSectionsUpperStarMap, Category.assoc]
  rw [eL.hom.naturality_assoc k]
  change eL.hom.app F ≫ k.hom.app (op (⊤_ Y.Etale)) ≫
      (adj.unit.app F').hom.app (op (⊤_ Y.Etale)) ≫
      ((upperStar A m).obj F').obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ =
    eL.hom.app F ≫ (adj.unit.app F).hom.app (op (⊤_ Y.Etale)) ≫
      ((upperStar A m).obj F).obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ ≫ (Sheaf.Γ X.smallEtaleTopology A).map ((upperStar A m).map k)
  rw [reassoc_of% hu]
  have hn := ((upperStar A m).map k).hom.naturality
    (PreservesTerminal.iso m.Etale).inv.op
  change ((upperStar A m).obj F).obj.map
      (PreservesTerminal.iso m.Etale).inv.op ≫
      ((upperStar A m).map k).hom.app (op (⊤_ X.Etale)) =
    ((lowerStar A m).map ((upperStar A m).map k)).hom.app
      (op (⊤_ Y.Etale)) ≫
      ((upperStar A m).obj F').obj.map
        (PreservesTerminal.iso m.Etale).inv.op at hn
  rw [← reassoc_of% hn]
  have hk := eK.inv.naturality ((upperStar A m).map k)
  change ((upperStar A m).map k).hom.app (op (⊤_ X.Etale)) ≫ eK.inv.app _ =
    eK.inv.app _ ≫ (Sheaf.Γ X.smallEtaleTopology A).map ((upperStar A m).map k) at hk
  rw [hk]

end GlobalSections

variable (Λ : Type (u + 1)) [CommRing Λ]

section StrictlyHenselian

variable (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]

/-- Over a strictly henselian local ring `R`, the unit of the adjunction between the constant
sheaf functor and the sections over `Spec R` is an isomorphism: sheafification does not change
sections over `Spec R`. -/
instance Etale.isIso_unit_constantSheafAdj_etaleTerminal :
    IsIso (constantSheafAdj (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (Scheme.isTerminalEtaleTerminal R)).unit := by
  have (M : ModuleCat.{u + 1} Λ) : IsIso ((constantSheafAdj (Spec (.of R)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) (Scheme.isTerminalEtaleTerminal R)).unit.app M) := by
    rw [constantSheafAdj, Adjunction.comp_unit_app, sheafificationAdjunction_unit_app]
    have : IsIso ((constantPresheafAdj (ModuleCat.{u + 1} Λ)
        (Scheme.isTerminalEtaleTerminal R)).unit.app M) := by
      rw [constantPresheafAdj_unit_app]
      infer_instance
    have : IsIso ((toSheafify (Spec (.of R)).smallEtaleTopology
        ((Functor.const _).obj M)).app (op (Scheme.etaleTerminal R))) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (Presheaf.bijective_app_of_forall_id_mem (J := (Spec (.of R)).smallEtaleTopology) _
          (Scheme.etaleTerminal R)
          (id_mem_of_mem_smallEtaleTopology_of_isStrictlyHenselianLocalRing R))
    dsimp
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end StrictlyHenselian

/-- The free sheaf `Λ[T]` on a terminal object `T` of the small étale site is the constant
sheaf with value the free `Λ`-module on one generator. -/
noncomputable def Etale.freeSheafObjIsoOfIsTerminal {X : Scheme.{u}} {T : X.Etale}
    (hT : IsTerminal T) :
    (Etale.freeSheaf Λ X).obj T ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        ((ModuleCat.free Λ).obj PUnit) :=
  (presheafToSheaf _ _).mapIso (NatIso.ofComponents (fun V ↦ (ModuleCat.free Λ).mapIso
    (Equiv.toIso
      { toFun := fun _ ↦ PUnit.unit
        invFun := fun _ ↦ ULift.up (hT.from V.unop)
        left_inv := fun x ↦ ULift.ext (hT.hom_ext _ _)
        right_inv := fun _ ↦ rfl })) (fun f ↦ by
    dsimp
    rw [Category.comp_id, ← Functor.map_comp]
    rfl))


section ClosedPoint

variable (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]

/-- Over a strictly henselian local ring `R`, the sections over the closed point
`s₀ : Spec κ ⟶ Spec R` of the pullback `s₀^* G` are the sections of `G` over `Spec R`. -/
noncomputable def Etale.sectionsUpperStarResidueIso
    (G : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    G.obj.obj (op (Scheme.etaleTerminal R)) ≅
      ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ].obj
        G).obj.obj (op (etalePoint (IsLocalRing.ResidueField R))) :=
  have : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) G) :=
    Etale.isIso_globalSectionsUpperStarMap_of_henselianRing Λ (IsLocalRing.maximalIdeal R)
      (𝟙 _) _ (𝟙 _) (IsPullback.id_vert _) G
  ((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.isTerminalEtaleTerminal R)).app G).symm ≪≫
    asIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) G) ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).app _

/-- Over a strictly henselian local ring `R`, the pullback to the closed point of a sheaf
without nonzero sections over `Spec R` is zero. -/
lemma Etale.isZero_upperStar_residue_obj
    {G : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h : Subsingleton (G.obj.obj (op (Scheme.etaleTerminal R)))) :
    IsZero ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ].obj
      G) :=
  isZero_of_subsingleton_sections_of_isSepClosed _
    (Etale.sectionsUpperStarResidueIso Λ R G).symm.toLinearEquiv.toEquiv.subsingleton

/-- Over a strictly henselian local ring `R`, a morphism of sheaves which is bijective on
sections over `Spec R` becomes an isomorphism after pullback to the closed point. -/
lemma Etale.isIso_upperStar_residue_map
    {G G' : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : G ⟶ G')
    [IsIso (g.hom.app (op (Scheme.etaleTerminal R)))] :
    IsIso ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ].map
      g) := by
  have hnat := Etale.globalSectionsUpperStarMap_naturality
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) g
  have h₁ (F) : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) F) :=
    Etale.isIso_globalSectionsUpperStarMap_of_henselianRing Λ (IsLocalRing.maximalIdeal R)
      (𝟙 _) _ (𝟙 _) (IsPullback.id_vert _) F
  have hΓ : IsIso ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map g) :=
    (NatIso.isIso_map_iff (Sheaf.ΓNatIsoSheafSections _ _
      (Scheme.isTerminalEtaleTerminal R)) g).2 ‹_›
  have : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) G ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ].map
          g)) := by
    rw [← hnat]
    infer_instance
  have : IsIso ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
      ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ].map g)) :=
    IsIso.of_isIso_comp_left (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) G) _
  have : IsIso (((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ].map
      g).hom.app (op (etalePoint (IsLocalRing.ResidueField R)))) :=
    (NatIso.isIso_map_iff (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint) _).1 this
  exact isIso_of_isIso_app_etalePoint Λ _

end ClosedPoint

section DerivedSections

variable {Λ}

/-- The section over `W` of `H⁰(L)` induced by a morphism `Λ[W][0] ⟶ L`. -/
noncomputable def Etale.derivedHomToSections {X : Scheme.{u}} (W : X.Etale)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W) ⟶ L) :
    ((DerivedCategory.Plus.homologyFunctor _ 0).obj L).obj.obj (op W) :=
  Etale.freeSheafHomEquiv Λ W _
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).map β)

/-- Naturality of `AlgebraicGeometry.Etale.derivedHomToSections` in `L`. -/
lemma Etale.derivedHomToSections_comp {X : Scheme.{u}} (W : X.Etale)
    {L L' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : L ⟶ L')
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W) ⟶ L) :
    Etale.derivedHomToSections W L' (β ≫ φ) =
      ((DerivedCategory.Plus.homologyFunctor _ 0).map φ).hom.app (op W)
        (Etale.derivedHomToSections W L β) := by
  rw [Etale.derivedHomToSections, Etale.derivedHomToSections, Functor.map_comp,
    ← Category.assoc, Etale.freeSheafHomEquiv_comp]

/-- Over a strictly henselian local ring `R`, the sections over `Spec R` of `H⁰(L)` are the
morphisms `Λ[Spec R][0] ⟶ L`. -/
lemma Etale.bijective_derivedHomToSections (R : Type u) [CommRing R]
    [IsStrictlyHenselianLocalRing R]
    (L : DerivedCategory.Plus (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (Etale.derivedHomToSections (Scheme.etaleTerminal R) L) := by
  obtain ⟨_, _⟩ := Etale.isLocallyBijective_derivedHomToHomology L
  have hfun : Etale.derivedHomToSections (Scheme.etaleTerminal R) L =
      ⇑((Etale.derivedHomToHomology L ≫ Etale.freeSheafSections Λ _).app
        (op (Scheme.etaleTerminal R))) :=
    funext fun β ↦ Etale.freeSheafHomEquiv_apply Λ _ _ _
  rw [hfun]
  exact Presheaf.bijective_app_of_forall_id_mem (J := (Spec (.of R)).smallEtaleTopology) _
    (Scheme.etaleTerminal R)
    (id_mem_of_mem_smallEtaleTopology_of_isStrictlyHenselianLocalRing R)

end DerivedSections

section Unit

variable (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R))

/-- Over a strictly henselian local ring `R` and for `t : Spec Ω ⟶ Spec R` with `Ω` separably
closed, the pullback `t^*` is bijective on morphisms `Λ[Spec R] ⟶ M_{Spec R}` into a constant
sheaf: `Λ[Spec R]` is constant, and the constant sheaf functors on `Spec R` and `Spec Ω` are
fully faithful. -/
lemma Etale.bijective_upperStar_map_freeSheaf_constantSheaf (M : ModuleCat.{u + 1} Λ) :
    Function.Bijective ((t)^*[ModuleCat.{u + 1} Λ].map :
      ((Etale.freeSheaf Λ _).obj (Scheme.etaleTerminal R) ⟶
        (constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) → _) :=
  Functor.bijective_map_of_iso_left _
    (Etale.freeSheafObjIsoOfIsTerminal Λ (Scheme.isTerminalEtaleTerminal R))
    (Functor.bijective_map_of_fullyFaithful_of_iso
      (constantSheafAdj _ _ (Scheme.isTerminalEtaleTerminal R)).fullyFaithfulLOfIsIsoUnit
      (constantSheafAdj _ _ isTerminalEtalePoint).fullyFaithfulLOfIsIsoUnit (F' := 𝟭 _)
      (Scheme.upperStarConstantSheafIso _ t ≪≫ (Functor.leftUnitor _).symm)
      Function.bijective_id)

/-- Degree zero: the unit `M_Y ⟶ Rt_* t^* M_Y` induces a bijection on the sections over
`Y = Spec R` of `H⁰`. -/
lemma Etale.isIso_homologyFunctor_zero_map_unit_app_etaleTerminal (M : ModuleCat.{u + 1} Λ) :
    IsIso (((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            M)))).hom.app (op (Scheme.etaleTerminal R))) := by
  let adj := Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  let S := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((Etale.freeSheaf Λ _).obj (Scheme.etaleTerminal R))
  have h₂ : Function.Bijective (D+((t)^*[ModuleCat.{u + 1} Λ]).map :
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((Etale.freeSheaf Λ _).obj (Scheme.etaleTerminal R)) ⟶ K) → _) :=
    Functor.bijective_map_of_fullyFaithful_of_iso (Functor.FullyFaithful.ofFullyFaithful _)
      (Functor.FullyFaithful.ofFullyFaithful _)
      ((t)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusSingleFunctor 0)
      (Etale.bijective_upperStar_map_freeSheaf_constantSheaf Λ R t M)
  have h₃ : (fun β : S ⟶ K ↦ β ≫ adj.unit.app K) =
      (adj.homEquiv _ _) ∘ (D+((t)^*[ModuleCat.{u + 1} Λ]).map :
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.freeSheaf Λ _).obj (Scheme.etaleTerminal R)) ⟶ K) → _) :=
    funext fun β ↦ by
      rw [Function.comp_apply, Adjunction.homEquiv_unit]
      exact adj.unit.naturality β
  have h₄ : Function.Bijective (fun β : S ⟶ K ↦ β ≫ adj.unit.app K) := by
    rw [h₃]
    exact (adj.homEquiv _ _).bijective.comp h₂
  have key : ⇑(((DerivedCategory.Plus.homologyFunctor _ 0).map (adj.unit.app K)).hom.app
      (op (Scheme.etaleTerminal R))) ∘ Etale.derivedHomToSections (Scheme.etaleTerminal R) K =
      Etale.derivedHomToSections (Scheme.etaleTerminal R) _ ∘
        (fun β : S ⟶ K ↦ β ≫ adj.unit.app K) :=
    funext fun β ↦ (Etale.derivedHomToSections_comp _ _ β).symm
  rw [ConcreteCategory.isIso_iff_bijective,
    ← Function.Bijective.of_comp_iff _ (Etale.bijective_derivedHomToSections R K), key]
  exact (Etale.bijective_derivedHomToSections R _).comp h₄

omit [IsStrictlyHenselianLocalRing R] in
/-- Over a strictly henselian local ring `R` and for `t : Spec Ω ⟶ Spec R` with `Ω` separably
closed, the pullback `t^* Λ[Spec R]` of the free sheaf on the terminal object is projective: it
is a constant sheaf on the separably closed point `Spec Ω`. -/
lemma Etale.projective_upperStar_freeSheaf_etaleTerminal :
    Projective ((t)^*[ModuleCat.{u + 1} Λ].obj
      ((Etale.freeSheaf Λ _).obj (Scheme.etaleTerminal R))) :=
  Projective.of_iso (((Scheme.upperStarConstantSheafIso _ t).app _).symm ≪≫
      ((t)^*[ModuleCat.{u + 1} Λ]).mapIso
        (Etale.freeSheafObjIsoOfIsTerminal Λ (Scheme.isTerminalEtaleTerminal R)).symm)
    ((constantSheafAdj _ _ isTerminalEtalePoint).map_projective _
      (ModuleCat.projective_of_free (Finsupp.basisSingleOne)))

/-- Positive and negative degrees: for `L ≅ N[0]` in `D⁺(Spec Ω)`, the sheaf `R^q t_* L` on
`Spec R` has no nonzero sections over `Spec R` when `q ≠ 0`. These sections are those of the
presheaf `W ↦ Hom(t^* Λ[W][0], L[q])` at `W = Spec R`, and `t^* Λ[Spec R]` is projective. -/
lemma Etale.subsingleton_homologyFunctor_rightDerivedLowerStar_obj_etaleTerminal
    (N : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (L : DerivedCategory.Plus (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : L ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj N) {q : ℤ} (hq : q ≠ 0) :
    Subsingleton (((DerivedCategory.Plus.homologyFunctor _ q).obj
      (R+((t)_*[ModuleCat.{u + 1} Λ]).obj L)).obj.obj (op (Scheme.etaleTerminal R))) := by
  obtain ⟨_, _⟩ := Etale.isLocallyBijective_higherDirectImagePresheafToSheaf Λ t q L
  have hb := Presheaf.bijective_app_of_forall_id_mem (J := (Spec (.of R)).smallEtaleTopology)
    (Etale.higherDirectImagePresheafToSheaf Λ t q L) (Scheme.etaleTerminal R)
    (id_mem_of_mem_smallEtaleTopology_of_isStrictlyHenselianLocalRing R)
  have := Etale.projective_upperStar_freeSheaf_etaleTerminal Λ R t
  have hs : Subsingleton ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((t)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ _).obj (Scheme.etaleTerminal R))) ⟶
        L⟦q⟧) :=
    have := DerivedCategory.Plus.subsingleton_hom_shift_of_projective
      ((t)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ _).obj (Scheme.etaleTerminal R)))
      N hq
    ((Iso.refl _).homCongr ((shiftFunctor _ q).mapIso e)).subsingleton
  exact @Function.Surjective.subsingleton _ _ _ hs hb.2

end Unit

/-- **The unit at a constant sheaf over a strictly henselian local ring.** Let `R` be a strictly
henselian local ring with closed point `s₀ : Spec κ ⟶ Spec R` and let `t : Spec Ω ⟶ Spec R` be
a morphism from the spectrum of a separably closed field. For every `Λ`-module `M`, the
pullback along `s₀` of the unit `M_Y[0] ⟶ Rt_* t^* M_Y[0]` of the derived adjunction
`t^* ⊣ Rt_*` at the constant sheaf `M_Y` on `Y = Spec R` is an isomorphism.

On homology sheaves on `Spec κ`, which are determined by their global sections, that is by the
sections over `Spec R` of the homology sheaves on `Y`
(`AlgebraicGeometry.Etale.isIso_upperStar_residue_map`): in degree `0` the unit induces the
bijection `t^* : Hom(Λ_Y, M_Y) ⟶ Hom(Λ_Ω, M_Ω)`
(`AlgebraicGeometry.Etale.isIso_homologyFunctor_zero_map_unit_app_etaleTerminal`), and in
degrees `q ≠ 0` both sides vanish
(`AlgebraicGeometry.Etale.subsingleton_homologyFunctor_rightDerivedLowerStar_obj_etaleTerminal`).
-/
theorem Etale.isIso_upperStar_map_unit_constantSheaf_of_isStrictlyHenselianLocalRing
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso (D+((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  refine (NatIso.isIso_map_iff ((Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusHomologyFunctorIso n)
      _).1 ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have := Etale.isIso_homologyFunctor_zero_map_unit_app_etaleTerminal Λ R t M
    exact Etale.isIso_upperStar_residue_map Λ R _
  · have hK : IsZero ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 n hn
      · exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 n hn
    exact isIso_of_source_target_iso_zero _
      (((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))^*[ModuleCat.{u + 1} Λ]).map_isZero
        hK).isoZero
      (Etale.isZero_upperStar_residue_obj Λ R
        (Etale.subsingleton_homologyFunctor_rightDerivedLowerStar_obj_etaleTerminal Λ R t _ _
          ((((t)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app _) hn)).isoZero

end AlgebraicGeometry
