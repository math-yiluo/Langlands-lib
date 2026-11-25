/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafRegularDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformExtBoundRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLattice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresentedField

/-!
# The uniform `Ext` bound for constructible `E`-sheaves, from `𝒪_E`, by dévissage

Blueprint `lemma-uniform-ext-bound`, coefficients `E`. Let `E ⊆ ℚ̄_ℓ` be a finite
subextension of `ℚ_ℓ` and `X` a noetherian scheme locally of finite type over a perfect field. If
constructible `𝒪_{E,X}`-modules satisfy the uniform `Ext` bound and `Hom(M[0], -[q])` factors
through filtered colimits for constructible `𝒪_{E,X}`-modules `M`, then constructible
`E_X`-modules satisfy the uniform `Ext` bound
(`ProEtale.hasUniformConstructibleExtBound_continuousMapRingObj_of_padicIntegersRingObj`).

Both arguments of `Hom(M[0], B[n])` are dévissé to the generators `Rc_* j_! Rc'_* L`, `L` a lisse
`E`-module on a connected regular noetherian scheme
(`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject_of_perfectField`). Such
`L` has a lattice (`ProEtale.exists_isLocallyFree_padicIntegers_extendScalars_iso`), so the
generators are `E ⊗ G₀` placed in degree `0` for constructible `𝒪_{E,X}`-modules `G₀`
(`ProEtale.exists_iso_singleFunctor_extendScalars_padicIntegersToPadicSubfield_of_lowerShriek`).
The classes of objects with a uniform vanishing are closed under extensions, and
`Ext^q_E(E ⊗ M₀, E ⊗ B₀)` is computed over `𝒪_E`
(`ProEtale.eq_zero_of_extendScalars_padicIntegersToPadicSubfield`). This does not use integral
models of bounded constructible `E`-complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

-- Prove the categorical vanishing arguments with an abstract category, so their
-- elaboration does not repeatedly unfold the concrete derived category of sheaves.
private lemma hom_eq_zero_of_target_iso {C : Type*} [Category C] [HasZeroMorphisms C]
    {A Y Y' : C} (e : Y ≅ Y') (h : ∀ f : A ⟶ Y, f = 0) (f : A ⟶ Y') : f = 0 :=
  (cancel_mono e.inv).1 ((h (f ≫ e.inv)).trans zero_comp.symm)

private lemma hom_eq_zero_of_source_iso {C : Type*} [Category C] [HasZeroMorphisms C]
    {A A' Y : C} (e : A ≅ A') (h : ∀ f : A ⟶ Y, f = 0) (f : A' ⟶ Y) : f = 0 :=
  (cancel_epi e.hom).1 ((h (e.hom ≫ f)).trans comp_zero.symm)

private lemma hom_eq_zero_of_distinguished {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (T : Triangle C) (hT : T ∈ distTriang C) {A : C}
    (h₁ : ∀ f : A ⟶ T.obj₁, f = 0) (h₃ : ∀ f : A ⟶ T.obj₃, f = 0)
    (f : A ⟶ T.obj₂) : f = 0 := by
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT f (h₃ _)
  exact hg.trans ((congrArg (fun k ↦ k ≫ T.mor₁) (h₁ g)).trans zero_comp)

private lemma hom_eq_zero_to_of_distinguished {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (T : Triangle C) (hT : T ∈ distTriang C) {B : C}
    (h₁ : ∀ f : T.obj₁ ⟶ B, f = 0) (h₃ : ∀ f : T.obj₃ ⟶ B, f = 0)
    (f : T.obj₂ ⟶ B) : f = 0 := by
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT f (h₁ _)
  exact hg.trans ((congrArg (fun k ↦ T.mor₂ ≫ k) (h₃ g)).trans comp_zero)

private lemma prop_of_exists_iso_image {C : Type*} [Category C] {D : Type*}
    (F : D → C) (Q : D → Prop) (P : C → Prop)
    (hiso : ∀ {Y Y'}, (Y ≅ Y') → P Y → P Y')
    (hF : ∀ M, Q M → P (F M)) {Y : C}
    (h : ∃ M, Q M ∧ Nonempty (Y ≅ F M)) : P Y := by
  obtain ⟨M, hM, ⟨e⟩⟩ := h
  exact hiso e.symm (hF M hM)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- The generators `Rc_* j_! Rc'_* L` of the dévissage over a perfect field
(`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject_of_perfectField`), for
`L` a lisse `E`-module on a connected regular noetherian scheme `S`, are isomorphic to `E ⊗ G`
placed in degree `0`, for a constructible `𝒪_{E,T}`-module `G`. Indeed `L ≅ E ⊗ L₀` for a locally
free `𝒪_{E,S}`-module `L₀` (`ProEtale.exists_isLocallyFree_padicIntegers_extendScalars_iso`), and
the extension of scalars commutes with `Rc_*`, `j_!` and `Rc'_*`, which are exact. -/
theorem exists_iso_singleFunctor_extendScalars_padicIntegersToPadicSubfield_of_lowerShriek
    {T D S : Scheme.{u}} [TopologicalSpace.NoetherianSpace T] (c : D ⟶ T) [IsClosedImmersion c]
    (V : D.Opens) (c' : S ⟶ V) [IsClosedImmersion c'] [IsNoetherian S] [IsRegular S]
    [ConnectedSpace S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) S))
    (hL : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) S) L) :
    ∃ G : Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) T),
      IsConstructibleModuleObject _ G ∧
      Nonempty ((R((c)_*⟦Profinite.continuousMapRingObj.{u} E.1⟧)).obj
        (D((V.ι)_!open⟦Profinite.continuousMapRingObj.{u} E.1⟧).obj
          ((R((c')_*⟦Profinite.continuousMapRingObj.{u} E.1⟧)).obj
            ((DerivedCategory.singleFunctor _ 0).obj L))) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((Mod.extendScalars (padicIntegersToPadicSubfield T ℓ E)).obj G)) := by
  have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨L', hL', ⟨e⟩⟩ := exists_isLocallyFree_padicIntegers_extendScalars_iso (ℓ := ℓ) L
    (CondensedRing.ContinuousMapRingObj.isLocallyFree_of_isLocallyFinitelyPresented ℓ E S hL)
  refine ⟨(c)_*⟦Profinite.padicIntegersRingObj.{u} ℓ E.1⟧.obj
    ((V.ι)_!open⟦Profinite.padicIntegersRingObj.{u} ℓ E.1⟧.obj
      ((c')_*⟦Profinite.padicIntegersRingObj.{u} ℓ E.1⟧.obj L')), ?_, ⟨?_⟩⟩
  · exact isConstructibleModuleObject_lowerStar_of_isClosedImmersion _ c
      (isConstructibleModuleObject_openImmersionLowerShriek_obj _ V.ι _
        (isConstructibleModuleObject_lowerStar_of_isClosedImmersion _ c'
          hL'.isConstructibleModuleObject))
  -- the derived functor `L(E ⊗ -)` is not written explicitly: synthesizing its instances over
  -- `𝒪_E` does not terminate, so it is obtained by unification with the isomorphisms below
  let eV := (derivedExtendScalarsLowerStarIsoOfIsClosedImmersion _
    (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E) c'
      ((DerivedCategory.singleFunctor _ 0).obj L')).symm
  let eD := ((derivedOpenImmersionShriekIso (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E)
    V.ι).app ((R((c')_*⟦Profinite.padicIntegersRingObj.{u} ℓ E.1⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj L'))).symm
  let eC := (derivedExtendScalarsLowerStarIsoOfIsClosedImmersion _
    (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E) c
      ((D((V.ι)_!open⟦Profinite.padicIntegersRingObj.{u} ℓ E.1⟧)).obj
        ((R((c')_*⟦Profinite.padicIntegersRingObj.{u} ℓ E.1⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj L')))).symm
  exact (R((c)_*⟦_⟧)).mapIso ((D((V.ι)_!open⟦_⟧)).mapIso
      ((R((c')_*⟦_⟧)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e.symm ≪≫
        (leftDerivedExtendScalarsSingleFunctorIso ℓ E L').symm) ≪≫ eV) ≪≫ eD) ≪≫ eC ≪≫
    Functor.mapIso _ (lowerShriekSingleIso _ c V c' L') ≪≫
    leftDerivedExtendScalarsSingleFunctorIso ℓ E _

/-- Let `G₀` be a constructible `𝒪_{E,X}`-module on a scheme `X` locally of finite type over a
perfect field, such that `Hom(G₀[0], -[q])` factors through filtered colimits and the morphisms
`G₀[0] ⟶ B[n]` vanish for every constructible `𝒪_{E,X}`-module `B` and `n ≤ N`. Then the morphisms
`(E ⊗ G₀)[0] ⟶ B[n]` vanish for every constructible `E_X`-module `B` and `n ≤ N`, by dévissage of
`B` (`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject_of_perfectField`) to
the generators `E ⊗ H₀`
(`ProEtale.exists_iso_singleFunctor_extendScalars_padicIntegersToPadicSubfield_of_lowerShriek`),
for which this is `ProEtale.eq_zero_of_extendScalars_padicIntegersToPadicSubfield`. -/
theorem eq_zero_of_extendScalars_padicIntegersToPadicSubfield_of_perfectField {k : Type u}
    [Field k] [PerfectField k] {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    {G₀ : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)}
    (hc : DerivedCategory.HomFactorsThroughFilteredColimits.{u + 1}
      ((DerivedCategory.singleFunctor _ 0).obj G₀)) (N : ℤ)
    (hN : ∀ B, IsConstructibleModuleObject _ B → ∀ n ≤ N,
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj G₀ ⟶ (DerivedCategory.singleFunctor _ n).obj B,
        f = 0)
    (B : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X))
    (hB : IsConstructibleModuleObject _ B) (n : ℤ) (hn : n ≤ N)
    (f : (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj G₀) ⟶
      (DerivedCategory.singleFunctor _ n).obj B) :
    f = 0 := by
  let A := (DerivedCategory.singleFunctor _ 0).obj
    ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj G₀)
  let P : ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X))) :=
    fun Y ↦ ∀ m ≤ N, ∀ g : A ⟶ Y⟦-m⟧, g = 0
  have hiso : ∀ {Y Y'}, (Y ≅ Y') → P Y → P Y' :=
    fun {_ _} e hY m hm g ↦
      hom_eq_zero_of_target_iso ((shiftFunctor _ (-m)).mapIso e) (hY m hm) g
  have hP : P ((DerivedCategory.singleFunctor _ 0).obj B) := by
    refine CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject_of_perfectField
      (preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional ℓ E.1) aX P
      (fun Y hY m _ g ↦ ((shiftFunctor _ (-m)).map_isZero hY).eq_of_tgt _ _)
      hiso (fun Tr hTr h₁ h₃ m hm g ↦ ?_)
      (fun D c _ V S c' _ _ _ _ L hL ↦ ?_) B hB
    · exact hom_eq_zero_of_distinguished _ (Triangle.shift_distinguished Tr hTr (-m))
        (h₁ m hm) (h₃ m hm) g
    · refine prop_of_exists_iso_image _ _ P hiso ?_
        (exists_iso_singleFunctor_extendScalars_padicIntegersToPadicSubfield_of_lowerShriek
          ℓ E c V c' L hL)
      intro H₀ hH₀ m hm g
      let e := ((DerivedCategory.singleFunctors _).shiftIso (-m) m 0 (by omega)).app
        ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj H₀)
      exact hom_eq_zero_of_target_iso e.symm
        (eq_zero_of_extendScalars_padicIntegersToPadicSubfield ℓ E hc N hN H₀ hH₀ m hm) g
  let e := ((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app B
  exact hom_eq_zero_of_target_iso e (hP n hn) f

/-- Blueprint `lemma-uniform-ext-bound`, coefficients `E`: on a noetherian scheme
locally of finite type over a perfect field, the uniform `Ext` bound for constructible
`E_X`-modules follows from the uniform bound and the continuity of `Ext` for constructible
`𝒪_{E,X}`-modules. Both arguments of `Hom(M[0], B[n])` are dévissé to the generators `E ⊗ G₀`,
`G₀` a constructible `𝒪_{E,X}`-module
(`ProEtale.exists_iso_singleFunctor_extendScalars_padicIntegersToPadicSubfield_of_lowerShriek`). -/
theorem hasUniformConstructibleExtBound_continuousMapRingObj_of_padicIntegersRingObj
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsNoetherian X]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    (hb : HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X))
    (hc : HasConstructibleExtContinuity
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X) := by
  intro M hM
  let P : ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X))) :=
    fun K ↦ ∃ N : ℤ, ∀ B, IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) X) B → ∀ n ≤ N,
      ∀ f : K ⟶ (DerivedCategory.singleFunctor _ n).obj B, f = 0
  refine CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject_of_perfectField
    (preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional ℓ E.1) aX P
    (fun K hK ↦ ⟨0, fun B _ n _ f ↦ hK.eq_of_src _ _⟩) (fun {K K'} e hK ↦ ?_)
    (fun Tr hTr h₁ h₃ ↦ ?_) (fun D c _ V S c' _ _ _ _ L hL ↦ ?_) M hM
  · obtain ⟨N, hN⟩ := hK
    refine ⟨N, fun B hB n hn f ↦ ?_⟩
    exact hom_eq_zero_of_source_iso e (hN B hB n hn) f
  · obtain ⟨N₁, h₁⟩ := h₁
    obtain ⟨N₃, h₃⟩ := h₃
    refine ⟨min N₁ N₃, fun B hB n hn f ↦ ?_⟩
    exact hom_eq_zero_to_of_distinguished Tr hTr
      (h₁ B hB n (hn.trans (min_le_left _ _)))
      (h₃ B hB n (hn.trans (min_le_right _ _))) f
  · obtain ⟨G₀, hG₀, ⟨eY⟩⟩ :=
      exists_iso_singleFunctor_extendScalars_padicIntegersToPadicSubfield_of_lowerShriek ℓ E c V c'
        L hL
    obtain ⟨N, hN⟩ := hb G₀ hG₀
    refine ⟨N, fun B hB n hn f ↦ ?_⟩
    exact hom_eq_zero_of_source_iso eY.symm
      (eq_zero_of_extendScalars_padicIntegersToPadicSubfield_of_perfectField ℓ E aX
        (hc G₀ hG₀) N hN B hB n hn) f

end AlgebraicGeometry.ProEtale
