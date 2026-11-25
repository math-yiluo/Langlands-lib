/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RestrictExtendScalarsColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ClosedImmersionExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.LisseDescentFiniteSubfield
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived

/-!
# The uniform `Ext` bound for constructible `ℚ̄_ℓ`-sheaves, by dévissage

Blueprint `lemma-uniform-ext-bound`, coefficients `ℚ̄_ℓ`. Let `X` be a scheme with
noetherian underlying space. If, for every finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, constructible
`E_X`-modules satisfy the uniform `Ext` bound, so do constructible `ℚ̄_{ℓ,X}`-modules
(`ProEtale.hasUniformConstructibleExtBound_padicAlgClRingObj_of_padicSubfield`).

This proof does not use the 2-colimit description of `Dᵇc(X, ℚ̄_ℓ)`; instead both arguments of
`Hom(M[0], B[n])` are dévissé to the generators `Rc_* j_! Rc'_* L`, `L` lisse
(`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject`), which descend to
constructible sheaves `G` over finite subextensions by the descent of lisse sheaves
(`ProEtale.exists_iso_singleFunctor_extendScalars_of_lowerShriek`). The classes of objects with a
uniform vanishing are closed under extensions, so it remains to treat
`Hom((ℚ̄_ℓ ⊗ M)[0], (ℚ̄_ℓ ⊗ G)[n])` for constructible `K_X`-modules `M` and `G`: by adjunction this
is `Hom(M[0], Res(ℚ̄_ℓ ⊗ G)[n])`, and `Res(ℚ̄_ℓ ⊗ G) = colim_{F ⊇ K} Res(F ⊗ G)` is a filtered
colimit of constructible `K_X`-modules
(`CategoryTheory.Mod.isColimitRestrictExtendScalarsColimitCocone`), out of which `Hom(M[0], -[n])`
commutes (`homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject`)
(`ProEtale.eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjToPadicAlgCl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

open CondensedRing

section Adjunction

variable {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
  [IsCommMonObj R] [MonObj S] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]
  [PreservesFiniteLimits (Mod.extendScalars φ)]

/-- A morphism `(S ⊗_R M)[0] ⟶ Y[n]` vanishes as soon as all morphisms `M[0] ⟶ Res_R(Y)[n]`
do: they correspond under the derived adjunction between extension and restriction of
scalars. -/
lemma eq_zero_of_forall_eq_zero_comap
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (Y : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) (n : ℤ)
    (h : ∀ g : (DerivedCategory.singleFunctor _ 0).obj M ⟶
      (DerivedCategory.singleFunctor _ n).obj ((Mod.comap φ).obj Y), g = 0)
    (f : (DerivedCategory.singleFunctor _ 0).obj ((Mod.extendScalars φ).obj M) ⟶
      (DerivedCategory.singleFunctor _ n).obj Y) : f = 0 := by
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction φ
  let e := (Mod.extendScalars φ).singleFunctorCompLeftDerivedFunctorIso.app M
  let e' := ((Mod.comap φ).mapDerivedCategorySingleFunctor n).app Y
  have h₀ : adj.homEquiv _ _ (e.hom ≫ f) = 0 := by
    rw [← cancel_mono e'.hom, zero_comp]
    exact h _
  have h₁ : e.hom ≫ f = 0 := (adj.homEquiv _ _).injective (by
    rw [h₀, adj.homEquiv_unit, Functor.map_zero, comp_zero])
  rw [← cancel_epi e.hom, h₁, comp_zero]

end Adjunction

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Let `K ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` and `M` a constructible `K_X`-module on a
scheme `X` with noetherian underlying space, such that the morphisms `M[0] ⟶ B[n]` vanish for
every constructible `K_X`-module `B` and `n ≤ N`. Then the morphisms
`(ℚ̄_ℓ ⊗ M)[0] ⟶ (ℚ̄_ℓ ⊗ G)[n]` vanish for every constructible `K_X`-module `G` and `n ≤ N`:
they are the morphisms `M[0] ⟶ Res(ℚ̄_ℓ ⊗ G)[n]`, and `Res(ℚ̄_ℓ ⊗ G)` is the filtered colimit of
the constructible `K_X`-modules `Res(F ⊗ G)`, `F ⊇ K` finite, out of which `Hom(M[0], -[n])`
commutes. -/
theorem eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjToPadicAlgCl {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] {K : FiniteIntermediateField ℓ}
    {M G : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ K)}
    (hM : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ K) M)
    (hG : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ K) G) {N : ℤ}
    (hN : ∀ B, IsConstructibleModuleObject (padicSubfieldRingObj X ℓ K) B → ∀ n ≤ N,
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        (DerivedCategory.singleFunctor _ n).obj B, f = 0)
    {n : ℤ} (hn : n ≤ N)
    (f : (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ K)).obj M) ⟶
      (DerivedCategory.singleFunctor _ n).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ K)).obj G)) : f = 0 := by
  refine eq_zero_of_forall_eq_zero_comap _ M _ n (fun g ↦ ?_) f
  have hc := Mod.isColimitRestrictExtendScalarsColimitCocone
    (padicSubfieldAboveRingObjFunctor ℓ K X) (fun F ↦ padicSubfieldRingObjMap X ℓ F.property)
    (padicSubfieldRingObjMap_comp_padicSubfieldAboveRingObjFunctor_map ℓ K X) G
    (fun F ↦ padicSubfieldRingObjToPadicAlgCl X ℓ F.obj)
    (fun g ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (leOfHom ((ObjectProperty.ι _).map g)))
    (padicSubfieldRingObjToPadicAlgCl X ℓ K)
    (fun F ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ F.property)
    (isColimitPadicSubfieldAboveRingObjCocone ℓ K X)
  have hcont := (homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject
    _ (preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional ℓ K.1)
    (fun _ _ ↦ CondensedRing.homCommutesWithFilteredColimits_singleFunctor_continuousMapRingObj ℓ
      K.1 _) X M hM).homFactorsThroughFilteredColimits
  have : IsFiltered (AsSmall.{u + 1} (PadicSubfieldAbove ℓ K)) :=
    IsFiltered.of_equivalence AsSmall.equiv
  obtain ⟨i, g', rfl⟩ := hcont (AsSmall.{u + 1} (PadicSubfieldAbove ℓ K)) _ _
    (hc.whiskerEquivalence AsSmall.equiv.symm) n g
  rw [hN _ ?_ n hn g', zero_comp]
  exact CondensedRing.isConstructibleModuleObject_comap_padicSubfieldRingObjMap ℓ _
    (CondensedRing.IsConstructibleModuleObject.extendScalars _ hG)

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The pushforward along a closed immersion into a scheme with noetherian underlying space
preserves constructible module objects. -/
lemma isConstructibleModuleObject_lowerStar_of_isClosedImmersion {Z X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (i : Z ⟶ X) [IsClosedImmersion i]
    {F : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
    (hF : IsConstructibleModuleObject (condensedRingObj Λ Z) F) :
    IsConstructibleModuleObject (condensedRingObj Λ X) ((i)_*⟦Λ⟧.obj F) :=
  IsConstructibleModuleObject.of_iso ((DerivedCategory.homologyFunctor _ 0).mapIso
      (rightDerivedLowerStarSingleIsoOfIsClosedImmersion Λ i F) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _)
    ((boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion Λ i
      (boundedConstructible_singleFunctor_obj Λ Z 0 F hF)).2 0)

/-- The complex `Rc_* j_! Rc'_* F` attached to closed immersions `c : D ⟶ T`, `c' : E ⟶ V` and
an open subscheme `V` of `D` is the sheaf `c_* j_! c'_* F` placed in degree `0`. -/
noncomputable def lowerShriekSingleIso {T D E : Scheme.{u}} [TopologicalSpace.NoetherianSpace T]
    (c : D ⟶ T) [IsClosedImmersion c] (V : D.Opens) [TopologicalSpace.NoetherianSpace V]
    (c' : E ⟶ V) [IsClosedImmersion c']
    (F : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)) :
    (R((c)_*⟦Λ⟧)).obj (D((V.ι)_!open⟦Λ⟧).obj
        ((R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((c)_*⟦Λ⟧.obj ((V.ι)_!open⟦Λ⟧.obj
        ((c')_*⟦Λ⟧.obj F))) :=
  (R((c)_*⟦Λ⟧)).mapIso ((D((V.ι)_!open⟦Λ⟧)).mapIso
      (rightDerivedLowerStarSingleIsoOfIsClosedImmersion Λ c' F) ≪≫
    (((V.ι)_!open⟦Λ⟧).mapDerivedCategorySingleFunctor 0).app _) ≪≫
  rightDerivedLowerStarSingleIsoOfIsClosedImmersion Λ c _

end CondensedRing


/-- The generators `Rc_* j_! Rc'_* L` of the dévissage, for `L` a lisse `ℚ̄_ℓ,E`-module, descend to
constructible sheaves over a finite subextension: they are isomorphic to `ℚ̄_ℓ ⊗ G` placed in
degree `0`, for a constructible `H_T`-module `G`. Indeed `L ≅ ℚ̄_ℓ ⊗ L_H` for a lisse
`H_E`-module `L_H` (`ProEtale.FiniteSubfieldDescent.exists_isLocallyFree_extendScalars_iso`), and
the extension of scalars commutes with `Rc_*`, `j_!` and `Rc'_*`. -/
theorem exists_iso_singleFunctor_extendScalars_of_lowerShriek {T D E : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace T] (c : D ⟶ T) [IsClosedImmersion c] (V : D.Opens)
    (c' : E ⟶ V) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (padicAlgClRingObj E ℓ))
    (hL : IsLocallyFinitelyPresented (padicAlgClRingObj E ℓ) L) :
    ∃ (H : FiniteIntermediateField ℓ)
      (G : Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ H)),
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ H) G ∧
      Nonempty ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        (D((V.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj L))) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ H)).obj G)) := by
  have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace E := c'.isClosedEmbedding.isInducing.noetherianSpace
  obtain ⟨H, L', hL', ⟨e⟩⟩ := FiniteSubfieldDescent.exists_isLocallyFree_extendScalars_iso ℓ E L
    (isLocallyFree_of_isLocallyFinitelyPresented_of_noetherianSpace ℓ E hL)
  let a := Profinite.padicSubfieldRingObjToPadicAlgCl ℓ H
  let ΛH := Profinite.continuousMapRingObj H.1
  refine ⟨H, (c)_*⟦ΛH⟧.obj ((V.ι)_!open⟦ΛH⟧.obj ((c')_*⟦ΛH⟧.obj L')), ?_, ⟨?_⟩⟩
  · exact isConstructibleModuleObject_lowerStar_of_isClosedImmersion ΛH c
      (isConstructibleModuleObject_openImmersionLowerShriek_obj ΛH V.ι _
        (isConstructibleModuleObject_lowerStar_of_isClosedImmersion ΛH c'
          hL'.isConstructibleModuleObject))
  · let eE := (Mod.extendScalars (coefficientMap a E)).singleFunctorCompLeftDerivedFunctorIso.app L'
    let eT := (Mod.extendScalars (coefficientMap a T)).singleFunctorCompLeftDerivedFunctorIso.app
      ((c)_*⟦ΛH⟧.obj ((V.ι)_!open⟦ΛH⟧.obj ((c')_*⟦ΛH⟧.obj L')))
    let eV := (derivedExtendScalarsLowerStarIsoOfIsClosedImmersion ΛH a c'
      ((DerivedCategory.singleFunctor _ 0).obj L')).symm
    let eD := ((derivedOpenImmersionShriekIso a V.ι).app
      ((R((c')_*⟦ΛH⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L'))).symm
    let eC := (derivedExtendScalarsLowerStarIsoOfIsClosedImmersion ΛH a c
      ((D((V.ι)_!open⟦ΛH⟧)).obj
        ((R((c')_*⟦ΛH⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L')))).symm
    exact (R((c)_*⟦_⟧)).mapIso ((D((V.ι)_!open⟦_⟧)).mapIso
        ((R((c')_*⟦_⟧)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e.symm ≪≫ eE.symm) ≪≫
          eV) ≪≫ eD) ≪≫ eC ≪≫
      (L(Mod.extendScalars (coefficientMap a T))).mapIso (lowerShriekSingleIso ΛH c V c' L') ≪≫
      eT

/-- The extension of scalars `ℚ̄_ℓ ⊗_{E_X} M` along `E_X ⟶ ℚ̄_ℓ,X` is `ℚ̄_ℓ ⊗_{F_X} (F_X ⊗_{E_X} M)`
for finite subextensions `E ≤ F`. -/
noncomputable def extendScalarsPadicSubfieldCompIso (X : Scheme.{u})
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj M ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).obj
        ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj M) :=
  ((Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).symm ≪≫
    Mod.extendScalarsComp _ _).app M

/-- The uniform vanishing of `Hom(M[0], -[n])`, `n ≤ N`, on constructible `H_X`-modules passes to
`F_X ⊗ M` and constructible `F_X`-modules, for `H ≤ F`, by adjunction: the restriction of scalars
of a constructible `F_X`-module is a constructible `H_X`-module. -/
lemma eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjMap {X : Scheme.{u}}
    {H F : FiniteIntermediateField ℓ} (h : H ≤ F)
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ H)} {N : ℤ}
    (hN : ∀ B, IsConstructibleModuleObject (padicSubfieldRingObj X ℓ H) B → ∀ n ≤ N,
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        (DerivedCategory.singleFunctor _ n).obj B, f = 0)
    (B : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F))
    (hB : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ F) B) (n : ℤ) (hn : n ≤ N)
    (f : (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj M) ⟶
      (DerivedCategory.singleFunctor _ n).obj B) : f = 0 :=
  eq_zero_of_forall_eq_zero_comap _ M B n
    (hN _ (isConstructibleModuleObject_comap_padicSubfieldRingObjMap ℓ h hB) n hn) f

/-- Let `M` be a constructible `H_X`-module such that the morphisms `M[0] ⟶ B[n]` vanish for every
constructible `H_X`-module `B` and `n ≤ N`. Then the morphisms `(ℚ̄_ℓ ⊗ M)[0] ⟶ (ℚ̄_ℓ ⊗ G)[n]`
vanish for every constructible `H'_X`-module `G`, `H'` another finite subextension, and `n ≤ N`:
both sides are extensions of scalars from a common finite subextension `K ⊇ H, H'`. -/
theorem eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjToPadicAlgCl' {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] {H H' : FiniteIntermediateField ℓ}
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ H)}
    (hM : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ H) M) {N : ℤ}
    (hN : ∀ B, IsConstructibleModuleObject (padicSubfieldRingObj X ℓ H) B → ∀ n ≤ N,
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        (DerivedCategory.singleFunctor _ n).obj B, f = 0)
    {G : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ H')}
    (hG : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ H') G)
    {n : ℤ} (hn : n ≤ N)
    (f : (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ H)).obj M) ⟶
      (DerivedCategory.singleFunctor _ n).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ H')).obj G)) : f = 0 := by
  obtain ⟨K, hK, hK'⟩ := exists_le_le ℓ H H'
  let e := (DerivedCategory.singleFunctor _ 0).mapIso (extendScalarsPadicSubfieldCompIso ℓ X hK M)
  let e' := (DerivedCategory.singleFunctor _ n).mapIso
    (extendScalarsPadicSubfieldCompIso ℓ X hK' G)
  have h₀ := eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjToPadicAlgCl ℓ
    (IsConstructibleModuleObject.extendScalars (Profinite.padicSubfieldRingObjMap ℓ hK) hM)
    (IsConstructibleModuleObject.extendScalars (Profinite.padicSubfieldRingObjMap ℓ hK') hG)
    (eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjMap ℓ hK hN) hn
    (e.inv ≫ f ≫ e'.hom)
  rw [← cancel_epi e.inv, ← cancel_mono e'.hom, Category.assoc, h₀, comp_zero, zero_comp]

/-- Let `M` be a constructible `H_X`-module on a scheme `X` with noetherian underlying space,
such that the morphisms `M[0] ⟶ B[n]` vanish for every constructible `H_X`-module `B` and
`n ≤ N`. Then the morphisms `(ℚ̄_ℓ ⊗ M)[0] ⟶ B[n]` vanish for every constructible
`ℚ̄_ℓ,X`-module `B` and `n ≤ N`, by dévissage of `B`
(`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject`) to the
generators `ℚ̄_ℓ ⊗ G`, `G` a constructible sheaf over a finite subextension
(`ProEtale.exists_iso_singleFunctor_extendScalars_of_lowerShriek`). -/
theorem eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjToPadicAlgCl_of_constructible
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] {H : FiniteIntermediateField ℓ}
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ H)}
    (hM : IsConstructibleModuleObject (padicSubfieldRingObj X ℓ H) M) {N : ℤ}
    (hN : ∀ B, IsConstructibleModuleObject (padicSubfieldRingObj X ℓ H) B → ∀ n ≤ N,
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        (DerivedCategory.singleFunctor _ n).obj B, f = 0)
    (B : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hB : IsConstructibleModuleObject (padicAlgClRingObj X ℓ) B) (n : ℤ) (hn : n ≤ N)
    (f : (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ H)).obj M) ⟶
      (DerivedCategory.singleFunctor _ n).obj B) : f = 0 := by
  let A := (DerivedCategory.singleFunctor _ 0).obj
    ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ H)).obj M)
  let P : ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))) :=
    fun Y ↦ ∀ m ≤ N, ∀ g : A ⟶ Y⟦-m⟧, g = 0
  have hP : P ((DerivedCategory.singleFunctor _ 0).obj B) := by
    refine prop_singleFunctor_of_isConstructibleModuleObject
      (fun Y ↦ preservesFiniteLimits_tensorLeft_padicAlgClRingObj Y ℓ) P
      (fun Y hY m _ g ↦ ((shiftFunctor _ (-m)).map_isZero hY).eq_of_tgt _ _)
      (fun {Y Y'} e hY m hm g ↦ ?_) (fun Tr hTr h₁ h₃ m hm g ↦ ?_)
      (fun D c _ V E c' _ L hL m hm g ↦ ?_) B hB
    · rw [← cancel_mono ((shiftFunctor _ (-m)).map e.inv), zero_comp]
      exact hY m hm _
    · obtain ⟨g', rfl⟩ := Triangle.coyoneda_exact₂ _ (Triangle.shift_distinguished Tr hTr (-m)) g
        (h₃ m hm _)
      rw [h₁ m hm g', zero_comp]
    · obtain ⟨H', G, hG, ⟨eY⟩⟩ := exists_iso_singleFunctor_extendScalars_of_lowerShriek ℓ c V c'
        L hL
      let e := (shiftFunctor _ (-m)).mapIso eY ≪≫
        ((DerivedCategory.singleFunctors _).shiftIso (-m) m 0 (by omega)).app _
      rw [← cancel_mono e.hom, zero_comp]
      exact eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjToPadicAlgCl' ℓ hM hN hG hm _
  let e := ((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app B
  rw [← cancel_mono e.inv, zero_comp]
  exact hP n hn _

/-- Blueprint `lemma-uniform-ext-bound`, coefficients `ℚ̄_ℓ`: the uniform `Ext`
bound for constructible `ℚ̄_{ℓ,X}`-modules follows from the uniform bound over the finite
subextensions `E ⊆ ℚ̄_ℓ`. Same statement as
`ProEtale.hasUniformConstructibleExtBound_padicAlgClRingObj_of_padicSubfield`,
proved by dévissage of both arguments instead of the 2-colimit description of `Dᵇc(X, ℚ̄_ℓ)`. -/
theorem hasUniformConstructibleExtBound_padicAlgClRingObj_of_padicSubfield
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (h : ∀ E : FiniteIntermediateField ℓ, HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X)) :
    HasUniformConstructibleExtBound (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X) := by
  intro M hM
  let P : ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))) :=
    fun K ↦ ∃ N : ℤ, ∀ B, IsConstructibleModuleObject (padicAlgClRingObj X ℓ) B → ∀ n ≤ N,
      ∀ f : K ⟶ (DerivedCategory.singleFunctor _ n).obj B, f = 0
  refine prop_singleFunctor_of_isConstructibleModuleObject
    (fun Y ↦ preservesFiniteLimits_tensorLeft_padicAlgClRingObj Y ℓ) P
    (fun K hK ↦ ⟨0, fun B _ n _ f ↦ hK.eq_of_src _ _⟩) (fun {K K'} e hK ↦ ?_)
    (fun Tr hTr h₁ h₃ ↦ ?_) (fun D c _ V E c' _ L hL ↦ ?_) M hM
  · obtain ⟨N, hN⟩ := hK
    refine ⟨N, fun B hB n hn f ↦ ?_⟩
    rw [← cancel_epi e.hom, comp_zero]
    exact hN B hB n hn _
  · obtain ⟨N₁, h₁⟩ := h₁
    obtain ⟨N₃, h₃⟩ := h₃
    refine ⟨min N₁ N₃, fun B hB n hn f ↦ ?_⟩
    obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₂ _ hTr f
      (h₁ B hB n (hn.trans (min_le_left _ _)) _)
    rw [h₃ B hB n (hn.trans (min_le_right _ _)) g, comp_zero]
  · obtain ⟨H, G, hG, ⟨eY⟩⟩ := exists_iso_singleFunctor_extendScalars_of_lowerShriek ℓ c V c' L hL
    obtain ⟨N, hN⟩ := h H G hG
    refine ⟨N, fun B hB n hn f ↦ ?_⟩
    rw [← cancel_epi eY.inv, comp_zero]
    exact eq_zero_of_singleFunctor_extendScalars_padicSubfieldRingObjToPadicAlgCl_of_constructible
      ℓ hG hN B hB n hn _

end AlgebraicGeometry.ProEtale

