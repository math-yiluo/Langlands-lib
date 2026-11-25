/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift
import all WeilConjectures.AlgebraicGeometry.DerivedAdjunctionCommShift
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-!
# Restriction of sections of homology sheaves over a strictly henselian local ring

Let `R` be a strictly henselian local ring with closed point `s₀ : Spec κ ⟶ Spec R`, let
`t : Spec Ω ⟶ Spec R` be a geometric point and `K ∈ D⁺((Spec R)_ét, Λ)`. If the pullback to the
closed point of the unit `K ⟶ Rt_* t^* K` is an isomorphism, then for every `q` the restriction
of global sections `Γ(Spec R, Hᵠ(K)) ⟶ Γ(Spec Ω, t^* Hᵠ(K))` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_homology_of_isIso_unit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

/-- A separably closed field is a strictly henselian local ring. -/
theorem IsStrictlyHenselianLocalRing.of_isSepClosed (K : Type*) [Field K] [IsSepClosed K] :
    IsStrictlyHenselianLocalRing K :=
  ⟨IsSepClosed.of_ringEquiv (RingEquiv.ofBijective (IsLocalRing.residue K)
    ⟨(IsLocalRing.residue K).injective, IsLocalRing.residue_surjective⟩)⟩

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The isomorphism `H^n(F(A)[-n]) ≅ F(H^n(A[-n]))` given by
`F.mapDerivedCategoryPlusSingleFunctor` and `F.mapDerivedCategoryPlusHomologyFunctorIso` is
compatible with the identifications `A ≅ H^n(A[-n])`. -/
@[reassoc]
lemma mapDerivedCategoryPlusHomologyFunctorIso_inv_app_singleFunctor (n : ℤ) (A : C) :
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app (F.obj A) ≫
      (DerivedCategory.Plus.homologyFunctor D n).map
        ((F.mapDerivedCategoryPlusSingleFunctor n).inv.app A) ≫
      (F.mapDerivedCategoryPlusHomologyFunctorIso n).inv.app
        ((DerivedCategory.Plus.singleFunctor C n).obj A) =
    F.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app A) := by
  rw [← cancel_mono (F.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).hom.app
    A)), ← F.map_comp, Iso.inv_hom_id_app,
    ← F.mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor n A]
  simp [← Functor.map_comp_assoc]

/-- For `i : B ⟶ F(A)` and `β : A[0] ⟶ L`, the morphism `B ⟶ F(H⁰(L))` given by
`B ⟶ F(A) ≅ F(H⁰(A[0])) ⟶ F(H⁰(L))` is the one given by `B ≅ H⁰(B[0])` and `H⁰` of
`B[0] ⟶ F(A)[0] ≅ F(A[0]) ⟶ F(L)`, followed by `H⁰(F(L)) ≅ F(H⁰(L))`. -/
lemma comp_map_singleFunctorCompHomologyFunctorIso_inv_app {A : C} {B : D} (i : B ⟶ F.obj A)
    {L : DerivedCategory.Plus C} (β : (DerivedCategory.Plus.singleFunctor C 0).obj A ⟶ L) :
    i ≫ F.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
      (DerivedCategory.Plus.homologyFunctor C 0).map β) =
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app B ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        ((DerivedCategory.Plus.singleFunctor D 0).map i ≫
          (F.mapDerivedCategoryPlusSingleFunctor 0).inv.app A ≫ F.mapDerivedCategoryPlus.map β)) ≫
      (F.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app L := by
  have n := (F.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.naturality β
  rw [Functor.comp_map, Functor.comp_map] at n
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    Category.assoc, n, ← mapDerivedCategoryPlusHomologyFunctorIso_inv_app_singleFunctor_assoc]
  have n' := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := D) 0).inv.naturality i
  rw [Functor.id_map, Functor.comp_map] at n'
  rw [reassoc_of% n']

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

section DerivedSections

/-- The defining formula of `AlgebraicGeometry.Etale.derivedHomToSections`. -/
lemma Etale.derivedHomToSections_eq {X : Scheme.{u}} (W : X.Etale)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W) ⟶ L) :
    Etale.derivedHomToSections W L β = Etale.freeSheafHomEquiv Λ W _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
        ((Etale.freeSheaf Λ X).obj W) ≫ (DerivedCategory.Plus.homologyFunctor _ 0).map β) :=
  rfl

/-- Naturality of `AlgebraicGeometry.Etale.derivedHomToSections` in the étale `X`-scheme: for
`v : W' ⟶ W`, the section over `W'` induced by `Λ[W'][0] ⟶ Λ[W][0] ⟶ L` is the restriction
of the section over `W` induced by `Λ[W][0] ⟶ L`. -/
lemma Etale.derivedHomToSections_map {X : Scheme.{u}} {W W' : X.Etale} (v : W' ⟶ W)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W) ⟶ L) :
    Etale.derivedHomToSections W' L
        ((DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ X).map v) ≫ β) =
      ((DerivedCategory.Plus.homologyFunctor _ 0).obj L).obj.map v.op
        (Etale.derivedHomToSections W L β) := by
  rw [Etale.derivedHomToSections, Etale.derivedHomToSections, ← Etale.freeSheafHomEquiv_map,
    Functor.map_comp]
  congr 1
  exact ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.naturality_assoc _
    _).symm

/-- The map `AlgebraicGeometry.Etale.derivedHomToSections` is bijective at `W'` as soon as it
is bijective at some `W ≅ W'`. -/
lemma Etale.bijective_derivedHomToSections_of_iso {X : Scheme.{u}} {W W' : X.Etale}
    (v : W' ≅ W) (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : Function.Bijective (Etale.derivedHomToSections W L)) :
    Function.Bijective (Etale.derivedHomToSections W' L) := by
  have key : Etale.derivedHomToSections W' L ∘
      (fun β ↦ (DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.freeSheaf Λ X).map v.hom) ≫ β) =
      ⇑(((DerivedCategory.Plus.homologyFunctor _ 0).obj L).obj.map v.hom.op) ∘
        Etale.derivedHomToSections W L :=
    funext fun β ↦ Etale.derivedHomToSections_map v.hom L β
  rw [← Function.Bijective.of_comp_iff _
    ⟨fun _ _ hab ↦ (cancel_epi _).1 hab, fun γ ↦ ⟨inv ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((Etale.freeSheaf Λ X).map v.hom)) ≫ γ, IsIso.hom_inv_id_assoc _ _⟩⟩, key]
  exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).comp h

/-- Over a strictly henselian local ring `R`, the sections over the terminal object `⊤_` of the
small étale site of `Spec R` of `H⁰(L)` are the morphisms `Λ[⊤_][0] ⟶ L`. -/
lemma Etale.bijective_derivedHomToSections_terminal (R : Type u) [CommRing R]
    [IsStrictlyHenselianLocalRing R]
    (L : DerivedCategory.Plus (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (Etale.derivedHomToSections (⊤_ (Spec (.of R)).Etale) L) :=
  Etale.bijective_derivedHomToSections_of_iso
    (terminalIsTerminal.uniqueUpToIso (Scheme.isTerminalEtaleTerminal R)) L
    (Etale.bijective_derivedHomToSections R L)

/-- The free sheaf `Λ[W ×_X Y]` maps to `h^* Λ[W]` by the inverse of
`AlgebraicGeometry.Etale.upperStarFreeSheafIso`, which is the image of the identity under
`AlgebraicGeometry.Etale.upperStarFreeSheafHomEquiv`. -/
lemma Etale.upperStarFreeSheafIso_inv {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale) :
    (Etale.upperStarFreeSheafIso Λ h W).inv = Etale.upperStarFreeSheafHomEquiv Λ h W _ (𝟙 _) :=
  rfl

/-- Sections over `W ×_X Y` corresponding to morphisms `Λ[W ×_X Y] ⟶ G` under
`AlgebraicGeometry.Etale.upperStarFreeSheafHomEquiv` are those of `h_* G` over `W`
corresponding to the adjoint morphisms `Λ[W] ⟶ h_* G`. -/
lemma Etale.freeSheafHomEquiv_upperStarFreeSheafHomEquiv {X Y : Scheme.{u}} (h : Y ⟶ X)
    (W : X.Etale) (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (a : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) :
    Etale.freeSheafHomEquiv Λ (h.Etale.obj W) G (Etale.upperStarFreeSheafHomEquiv Λ h W G a) =
      Etale.freeSheafHomEquiv Λ W _ ((upperStarLowerStarAdjunction _ h).homEquiv _ _ a) :=
  Equiv.apply_symm_apply _ _

/-- The section over `W` of `h_* h^* G` given by the composite of `a : Λ[W] ⟶ G` with the unit
of `h^* ⊣ h_*` is the section over `W ×_X Y` of `h^* G` given by
`Λ[W ×_X Y] ≅ h^* Λ[W] ⟶ h^* G`. -/
lemma Etale.freeSheafHomEquiv_comp_unit {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale)
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (a : (Etale.freeSheaf Λ X).obj W ⟶ G) :
    Etale.freeSheafHomEquiv Λ W _ (a ≫ (upperStarLowerStarAdjunction _ h).unit.app G) =
      Etale.freeSheafHomEquiv Λ (h.Etale.obj W) _
        ((Etale.upperStarFreeSheafIso Λ h W).inv ≫ (h)^*[ModuleCat.{u + 1} Λ].map a) := by
  rw [Etale.upperStarFreeSheafIso_inv, ← Etale.upperStarFreeSheafHomEquiv_comp, Category.id_comp,
    Etale.freeSheafHomEquiv_upperStarFreeSheafHomEquiv, Adjunction.homEquiv_unit,
    Adjunction.unit_naturality]
  rfl

/-- The pullback along `m : Y ⟶ X` of the section over `W` of `H⁰(L)` induced by
`β : Λ[W][0] ⟶ L` is the section over `W ×_X Y` of `H⁰(m^* L) ≅ m^* H⁰(L)` induced by
`Λ[W ×_X Y][0] ≅ m^*(Λ[W][0]) ⟶ m^* L`. -/
lemma Etale.upperStarLowerStarAdjunction_unit_app_derivedHomToSections {X Y : Scheme.{u}}
    (m : Y ⟶ X) (W : X.Etale)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W) ⟶ L) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) m).unit.app
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)).hom.app (op W)
        (Etale.derivedHomToSections W L β) =
      ((((m)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app
        L).hom.app (op (m.Etale.obj W))
        (Etale.derivedHomToSections _ (D+((m)^*[ModuleCat.{u + 1} Λ]).obj L)
          ((DerivedCategory.Plus.singleFunctor _ 0).map (Etale.upperStarFreeSheafIso Λ m W).inv ≫
            (((m)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
            D+((m)^*[ModuleCat.{u + 1} Λ]).map β)) := by
  rw [Etale.derivedHomToSections_eq, Etale.derivedHomToSections_eq]
  erw [← Etale.freeSheafHomEquiv_comp, ← Etale.freeSheafHomEquiv_comp]
  rw [Etale.freeSheafHomEquiv_comp_unit,
    Functor.comp_map_singleFunctorCompHomologyFunctorIso_inv_app]
  rfl

end DerivedSections

section GlobalSections

/-- The isomorphism `Λ[⊤][0] ≅ m^*(Λ[⊤][0])` for `m : Y ⟶ X`: the base change of the terminal
object of the small étale site of `X` is terminal, and the pullback of a free sheaf is the free
sheaf on the base change (`AlgebraicGeometry.Etale.upperStarFreeSheafIso`). -/
noncomputable def Etale.singleFreeSheafTerminalUpperStarIso {X Y : Scheme.{u}} (m : Y ⟶ X) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ Y).obj (⊤_ Y.Etale)) ≅
      D+((m)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj (⊤_ X.Etale))) :=
  (DerivedCategory.Plus.singleFunctor _ 0).mapIso ((Etale.freeSheaf Λ Y).mapIso
      (PreservesTerminal.iso m.Etale).symm ≪≫
        (Etale.upperStarFreeSheafIso Λ m (⊤_ X.Etale)).symm) ≪≫
    ((((m)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app _).symm

/-- The explicit form of `AlgebraicGeometry.Etale.singleFreeSheafTerminalUpperStarIso`. -/
lemma Etale.singleFreeSheafTerminalUpperStarIso_hom {X Y : Scheme.{u}} (m : Y ⟶ X) :
    (Etale.singleFreeSheafTerminalUpperStarIso (Λ := Λ) m).hom =
      (DerivedCategory.Plus.singleFunctor _ 0).map
          ((Etale.freeSheaf Λ Y).map (PreservesTerminal.iso m.Etale).inv) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          (Etale.upperStarFreeSheafIso Λ m (⊤_ X.Etale)).inv ≫
        (((m)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ := by
  simp [Etale.singleFreeSheafTerminalUpperStarIso]

/-- The pullback map on global sections of `H⁰(L)` along `m : Y ⟶ X`, on the global section
induced by `β : Λ[X][0] ⟶ L`: it is the global section of `H⁰(m^* L) ≅ m^* H⁰(L)` induced by
`Λ[Y][0] ≅ m^*(Λ[X][0]) ⟶ m^* L`. -/
lemma Etale.globalSectionsUpperStarMap_derivedHomToSections {X Y : Scheme.{u}} (m : Y ⟶ X)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj (⊤_ X.Etale)) ⟶
      L) :
    globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) m
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)
        ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          terminalIsTerminal).inv.app ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)
          (Etale.derivedHomToSections (⊤_ X.Etale) L β)) =
      (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).inv.app
          ((m)^*[ModuleCat.{u + 1} Λ].obj ((DerivedCategory.Plus.homologyFunctor _ 0).obj L))
        (((((m)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app
          L).hom.app (op (⊤_ Y.Etale))
          (Etale.derivedHomToSections (⊤_ Y.Etale) _
            ((Etale.singleFreeSheafTerminalUpperStarIso m).hom ≫
              D+((m)^*[ModuleCat.{u + 1} Λ]).map β))) := by
  have h₁ (y) : ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).hom.app ((DerivedCategory.Plus.homologyFunctor _ 0).obj L))
      (((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).inv.app ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) y) = y := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app, ConcreteCategory.id_apply]
  simp only [globalSectionsUpperStarMap, ConcreteCategory.comp_apply, h₁]
  congr 1
  rw [Etale.singleFreeSheafTerminalUpperStarIso_hom, Category.assoc, Category.assoc,
    Etale.derivedHomToSections_map]
  exact (congrArg _ (Etale.upperStarLowerStarAdjunction_unit_app_derivedHomToSections m _ L
    β)).trans (NatTrans.naturality_apply _ _ _).symm

/-- The pullback map on global sections along `m` is an isomorphism at `F'` as soon as it is
one at some `F ≅ F'`. -/
lemma Etale.isIso_globalSectionsUpperStarMap_of_iso {X Y : Scheme.{u}} (m : X ⟶ Y)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ≅ F')
    [IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) m F)] :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) m F') := by
  have : IsIso ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map e.hom ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) m F') := by
    rw [Etale.globalSectionsUpperStarMap_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map e.hom) _

/-- Over a strictly henselian local ring `R`, a morphism of sheaves whose pullback to the closed
point is an isomorphism is bijective on sections over `Spec R`. -/
lemma Etale.isIso_app_terminal_of_isIso_upperStar_residue_map (R : Type u) [CommRing R]
    [IsStrictlyHenselianLocalRing R]
    {G G' : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : G ⟶ G')
    [IsIso ((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ].map g)] :
    IsIso (g.hom.app (op (⊤_ (Spec (.of R)).Etale))) := by
  have h₁ (F) : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (closedGeometricPoint R) F) :=
    Etale.isIso_globalSectionsUpperStarMap_of_henselianRing Λ (IsLocalRing.maximalIdeal R)
      (𝟙 _) _ (𝟙 _) (IsPullback.id_vert _) F
  have : IsIso ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map g ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (closedGeometricPoint R) G') := by
    rw [Etale.globalSectionsUpperStarMap_naturality]
    infer_instance
  have : IsIso ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map g) :=
    IsIso.of_isIso_comp_right _ (globalSectionsUpperStarMap _ (closedGeometricPoint R) G')
  exact (NatIso.isIso_map_iff (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal) g).1 this

/-- **Degree zero.** Let `R` be a strictly henselian local ring, `t : Spec Ω ⟶ Spec R` with `Ω`
separably closed and `L ∈ D⁺((Spec R)_ét, Λ)` such that `H⁰` of the unit `L ⟶ Rt_* t^* L` is
bijective on sections over `Spec R`. Then `Γ(Spec R, H⁰(L)) ⟶ Γ(Spec Ω, t^* H⁰(L))` is an
isomorphism: both sides are the morphisms from `Λ[0]` to `L`, respectively to `t^* L`, and the map
between them is `t^*`, which composed with the adjunction is the composition with the unit. -/
theorem Etale.isIso_globalSectionsUpperStarMap_homology_zero_of_isIso_unit (R : Type u)
    [CommRing R] [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of R))
    (L : DerivedCategory.Plus (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : IsIso (((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app
        L)).hom.app (op (⊤_ (Spec (.of R)).Etale)))) :
    IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) := by
  have := IsStrictlyHenselianLocalRing.of_isSepClosed Ω
  let adj := Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t
  have h₁ : Function.Bijective (fun β : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((Etale.freeSheaf Λ _).obj (⊤_ (Spec (.of R)).Etale)) ⟶ L ↦ β ≫ adj.unit.app L) := by
    have key : ⇑(((DerivedCategory.Plus.homologyFunctor _ 0).map (adj.unit.app L)).hom.app
        (op (⊤_ (Spec (.of R)).Etale))) ∘ Etale.derivedHomToSections _ L =
        Etale.derivedHomToSections _ _ ∘ (fun β ↦ β ≫ adj.unit.app L) :=
      funext fun β ↦ (Etale.derivedHomToSections_comp _ _ β).symm
    exact (Function.Bijective.of_comp_iff' (Etale.bijective_derivedHomToSections_terminal R _)
      _).1 ((congrArg Function.Bijective key).mp
        (((ConcreteCategory.isIso_iff_bijective _).1 hL).comp
          (Etale.bijective_derivedHomToSections_terminal R L)))
  have h₂ : Function.Bijective (D+((t)^*[ModuleCat.{u + 1} Λ]).map :
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((Etale.freeSheaf Λ _).obj (⊤_ (Spec (.of R)).Etale)) ⟶ L) → _) := by
    have h₃ : (fun β : (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((Etale.freeSheaf Λ _).obj (⊤_ (Spec (.of R)).Etale)) ⟶ L ↦ β ≫ adj.unit.app L) =
        (adj.homEquiv _ _) ∘ D+((t)^*[ModuleCat.{u + 1} Λ]).map :=
      funext fun β ↦ by
        rw [Function.comp_apply, Adjunction.homEquiv_unit]
        exact adj.unit.naturality β
    exact (Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective _).1
      ((congrArg Function.Bijective h₃).mp h₁)
  let eR := Sheaf.ΓNatIsoSheafSections (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    terminalIsTerminal
  let eΩ := Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    terminalIsTerminal
  have key : ⇑(Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ∘
      (⇑(eR.inv.app ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ∘
        Etale.derivedHomToSections (⊤_ (Spec (.of R)).Etale) L) =
      (⇑(eΩ.inv.app
          ((t)^*[ModuleCat.{u + 1} Λ].obj ((DerivedCategory.Plus.homologyFunctor _ 0).obj L))) ∘
        ⇑(((((t)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app
          L).hom.app (op (⊤_ (Spec (.of Ω)).Etale))) ∘
        Etale.derivedHomToSections (⊤_ (Spec (.of Ω)).Etale) _) ∘
      (fun γ ↦ (Etale.singleFreeSheafTerminalUpperStarIso t).hom ≫ γ) ∘
        D+((t)^*[ModuleCat.{u + 1} Λ]).map :=
    funext fun β ↦ Etale.globalSectionsUpperStarMap_derivedHomToSections t L β
  rw [ConcreteCategory.isIso_iff_bijective]
  refine (Function.Bijective.of_comp_iff _
    (((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).comp
      (Etale.bijective_derivedHomToSections_terminal R L))).1
    ((congrArg Function.Bijective key).mpr ?_)
  refine (((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).comp
    (((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).comp
      (Etale.bijective_derivedHomToSections_terminal Ω _))).comp (Function.Bijective.comp ?_ h₂)
  exact ⟨fun _ _ h ↦ (cancel_epi _).1 h, fun γ ↦
    ⟨(Etale.singleFreeSheafTerminalUpperStarIso t).inv ≫ γ,
      (Etale.singleFreeSheafTerminalUpperStarIso t).hom_inv_id_assoc γ⟩⟩

end GlobalSections

/-- **Restriction of sections of homology sheaves to a geometric point of a strictly local
scheme.** Let `R` be a strictly henselian local ring, `t : Spec Ω ⟶ Spec R` a geometric point
and `K ∈ D⁺((Spec R)_ét, Λ)` such that the restriction to the closed point of the unit
`K ⟶ Rt_* t^* K` is an isomorphism. Then for every `q` the pullback of global sections
`Γ(Spec R, Hᵠ(K)) ⟶ Γ(Spec Ω, t^* Hᵠ(K))` is an isomorphism. -/
theorem Etale.isIso_globalSectionsUpperStarMap_homology_of_isIso_unit (R : Type u) [CommRing R]
    [IsStrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of R))
    (K : DerivedCategory.Plus (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsIso (D+((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app K)))
    (q : ℤ) :
    IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) t
      ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) := by
  have hKq : IsIso (D+((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app
        (K⟦q⟧))) := by
    rw [Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus] at hK ⊢
    have := derivedUnit_commShift (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t)
    have : IsIso (D+((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).map
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).derivedPlus.unit.app K)⟦q⟧')) :=
      (NatIso.isIso_map_iff ((D+((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ])).commShiftIso
        q) _).2 (Functor.map_isIso (shiftFunctor _ q) _)
    rw [NatTrans.app_shift _ q K, Functor.map_comp, Functor.map_comp]
    infer_instance
  have : IsIso ((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ].map
      ((DerivedCategory.Plus.homologyFunctor _ 0).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) t).unit.app
          (K⟦q⟧)))) :=
    (NatIso.isIso_map_iff
      (((closedGeometricPoint R)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso
        0) _).2 (Functor.map_isIso (DerivedCategory.Plus.homologyFunctor _ 0) _)
  have := Etale.isIso_globalSectionsUpperStarMap_homology_zero_of_isIso_unit R t (K⟦q⟧)
    (Etale.isIso_app_terminal_of_isIso_upperStar_residue_map R _)
  exact Etale.isIso_globalSectionsUpperStarMap_of_iso t
    ((((DerivedCategory.Plus.homologyFunctor _ 0).isoShiftZero ℤ).app (K⟦q⟧)).symm ≪≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).app K)

end AlgebraicGeometry
