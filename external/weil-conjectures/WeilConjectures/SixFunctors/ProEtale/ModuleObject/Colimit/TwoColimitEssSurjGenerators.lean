/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ClosedImmersionExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.LisseDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitEssSurjCone
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedLowerStarOpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresentedField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClFlat

/-!
# Descent of the generators `a_! L` of bounded constructible `ℚ̄_ℓ`-complexes

Let `ℓ` be a prime and `X` a scheme with noetherian underlying space. For a locally closed
immersion `a = j ∘ i : S ⟶ U ⟶ X` (`i` a closed immersion, `j` an open immersion) and a lisse
`ℚ̄_ℓ,S`-module `L`, write `a_! L = j_! Ri_* L` for the extension by zero of `L` placed in
degree `0`.

* `ProEtale.CondensedRing.boundedConstructible_le_of_lowerShriek_isLocallyFree` (blueprint
  `corollary-coefficient-heart-b--2`): every bounded constructible `ℚ̄_ℓ,X`-complex lies
  in the smallest class of complexes closed under isomorphisms and extensions in distinguished
  triangles and containing the shifts `(a_! L)[n]`. The class of `K` all of whose shifts lie in
  such a class is triangulated, so by the truncation dévissage
  (`ProEtale.prop_of_boundedConstructibleModule`) and the dévissage of constructible sheaves
  (`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject`) it suffices to
  treat the complexes `Rc_* V_! Rc'_* L`, `L` lisse, hence locally free. These are of the form
  `a_! L` for the open `U = X ∖ c(D ∖ V)`
  (`ProEtale.CondensedRing.rightDerivedLowerStarOpenImmersionLowerShriekSingleIso`).
* `ProEtale.descendsToPadicSubfield_lowerShriek`: each `a_! L` descends to a finite
  subextension. By the descent of lisse sheaves
  (`ProEtale.exists_isLocallyFree_extendScalars_iso`), `L ≅ ℚ̄_ℓ,S ⊗_{E_S} L_E` for a lisse
  `E_S`-module `L_E`; the complex `a_! L_E` is bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_openImmersionLowerShriek_obj_of_noetherianSpace`
  and `ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion`),
  and `T^X_{E,Ω} (a_! L_E) ≅ a_! L` by the (Shriek) isomorphism for the open immersion `j`
  (`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`) and the commutation of the extension
  of scalars with the pushforward along the closed immersion `i`
  (`ProEtale.CondensedRing.derivedExtendScalarsLowerStarIsoOfIsClosedImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

namespace CondensedRing

/-- The extension by zero along an open immersion `j : U ⟶ X` into a scheme with noetherian
underlying space, applied levelwise, preserves bounded constructible complexes: it is exact, so
it commutes with the cohomology sheaves, and it preserves zero objects and constructible module
objects (`ProEtale.CondensedRing.isConstructibleModuleObject_openImmersionLowerShriek_obj`). -/
lemma boundedConstructible_openImmersionLowerShriek_obj_of_noetherianSpace
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (j : U ⟶ X) [IsOpenImmersion j]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))} (hK : boundedConstructible (condensedRingObj Λ U) K) :
    boundedConstructible (condensedRingObj Λ X) ((D((j)_!open⟦Λ⟧)).obj K) := by
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ K).1 hK
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact ((j)_!open⟦Λ⟧.map_isZero (hab i hi)).of_iso
      ((Functor.mapDerivedCategoryHomologyFunctorIso _ i).app K).symm
  · exact (isConstructibleModuleObject_openImmersionLowerShriek_obj Λ j _ (hc n)).of_iso
      ((Functor.mapDerivedCategoryHomologyFunctorIso _ n).app K)
/-- A constructible module object placed in degree `n` is a bounded constructible complex. -/
lemma boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X : Scheme.{u}} (n : ℤ)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    boundedConstructible (condensedRingObj Λ X) ((DerivedCategory.singleFunctor _ n).obj M) := by
  refine ⟨⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩, fun i ↦ ?_⟩
  rcases lt_trichotomy i n with hi | rfl | hi
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isGE _ n i hi)
  · exact IsConstructibleModuleObject.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app M).symm hM
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isLE _ n i hi)

/-- For a flat coefficient change `a : Λ ⟶ Λ'`, an open immersion `j : U ⟶ X`, a closed
immersion `i : S ⟶ U` with `U` noetherian and a `Λ_S`-module `M`, the extension of scalars
commutes with `j_! Ri_*` on `M` placed in degree `0`:
`T^X (j_! Ri_* M) ≅ j_! Ri_* (Λ'_S ⊗_{Λ_S} M)`, by the (Shriek) isomorphism for `j` and
`ProEtale.CondensedRing.derivedExtendScalarsLowerStarIsoOfIsClosedImmersion`. -/
noncomputable def derivedExtendScalarsLowerShriekSingleIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    {U S X : Scheme.{u}} [TopologicalSpace.NoetherianSpace U] (j : U ⟶ X) [IsOpenImmersion j]
    (i : S ⟶ U) [IsClosedImmersion i]
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (L(Mod.extendScalars (coefficientMap a X))).obj
        ((D((j)_!open⟦Λ⟧)).obj ((R((i)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj M))) ≅
      (D((j)_!open⟦Λ'⟧)).obj ((R((i)_*⟦Λ'⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap a S)).obj M))) :=
  (derivedOpenImmersionShriekIso a j).app _ ≪≫ (D((j)_!open⟦Λ'⟧)).mapIso
    (derivedExtendScalarsLowerStarIsoOfIsClosedImmersion Λ a i _ ≪≫
      (R((i)_*⟦Λ'⟧)).mapIso ((Functor.singleFunctorCompLeftDerivedFunctorIso _).app M))

variable (ℓ : ℕ) [Fact ℓ.Prime]

open ZeroObject in
/-- Blueprint `corollary-coefficient-heart-b--2` (subsection
`corollary-coefficient-heart-b`): on a scheme `X` with noetherian underlying
space, every `K ∈ Dᵇc(X, ℚ̄_ℓ)` is obtained by finitely many cones from the objects
`(a_! L)[n]`, for `a = j ∘ i : S ⟶ U ⟶ X` a locally closed immersion (`i` a closed immersion,
`j` an open immersion), `L` a lisse `ℚ̄_ℓ,S`-module and `n ∈ ℤ`, where
`a_! L = j_! Ri_* L`. That is, `K` lies in every class `P` of objects of `D(ℚ̄_ℓ,X)` which is
closed under isomorphisms and extensions in distinguished triangles and contains these
objects.

This states only one direction of the blueprint node (the objects `(a_! L)[n]` generate
`Dᵇc`; that they lie in `Dᵇc` is not restated), and only for `Λ = ℚ̄_ℓ`. -/
theorem boundedConstructible_le_of_lowerShriek_isLocallyFree (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (P : ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicAlgClRingObj X ℓ)))) [P.IsClosedUnderIsomorphisms]
    (hext : ∀ T ∈ distTriang _, P T.obj₁ → P T.obj₃ → P T.obj₂)
    (hgen : ∀ {U S : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (i : S ⟶ U)
      [IsClosedImmersion i] (L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1})
        (padicAlgClRingObj S ℓ)), IsLocallyFree (padicAlgClRingObj S ℓ) L → ∀ n : ℤ,
      P ((shiftFunctor _ n).obj ((D((j)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        ((R((i)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj L)))))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)))
    (hK : boundedConstructible (padicAlgClRingObj X ℓ) K) : P K := by
  let P' : ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicAlgClRingObj X ℓ))) := fun K ↦ ∀ n : ℤ, P ((shiftFunctor _ n).obj K)
  have hiso {K K'} (e : K ≅ K') (h : P' K) : P' K' :=
    fun n ↦ P.prop_of_iso ((shiftFunctor _ n).mapIso e) (h n)
  have hext' (T) (hT : T ∈ distTriang _) (h₁ : P' T.obj₁) (h₃ : P' T.obj₃) : P' T.obj₂ :=
    fun n ↦ hext _ (Triangle.shift_distinguished T hT n) (h₁ n) (h₃ n)
  have hshift (K) (h : P' K) (m : ℤ) : P' ((shiftFunctor _ m).obj K) :=
    fun n ↦ P.prop_of_iso ((shiftFunctorAdd' _ m n (m + n) rfl).app K) (h (m + n))
  have hgen' {U S : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (i : S ⟶ U) [IsClosedImmersion i]
      (L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (padicAlgClRingObj S ℓ))
      (hL : IsLocallyFree (padicAlgClRingObj S ℓ) L) :
      P' ((D((j)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        ((R((i)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj L))) :=
    hgen j i L hL
  -- a zero object lies in `P'`, by the rotated contractible triangle `G ⟶ 0 ⟶ G[1] ⟶ G[1]`
  have h0 : P' 0 := by
    have hG := hgen' (𝟙 X) (𝟙 X) _ (isLocallyFree_of_isFree
      (M := Mod.finiteFree (padicAlgClRingObj X ℓ) 0) ⟨0, ⟨Iso.refl _⟩⟩)
    exact hiso (isZero_zero _).isoZero.symm
      (hext' _ (rot_of_distTriang _ (contractible_distinguished _)) hG (hshift _ hG 1))
  have hzero (K) (h : IsZero K) : P' K := hiso (h.isoZero ≪≫ (isZero_zero _).isoZero.symm).symm h0
  have : P'.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hiso e h⟩
  have : P'.IsTriangulated :=
    { exists_zero := ⟨0, isZero_zero _, h0⟩
      isStableUnderShiftBy m := ⟨fun K h ↦ hshift K h m⟩
      toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦ hext' T hT h₁ h₃ }
  refine P.prop_of_iso ((shiftFunctorZero _ ℤ).app K)
    (prop_of_boundedConstructibleModule P' (fun F hF ↦ ?_) hK 0)
  refine prop_singleFunctor_of_isConstructibleModuleObject
    (fun Y ↦ preservesFiniteLimits_tensorLeft_padicAlgClRingObj Y ℓ) P' hzero hiso hext'
    (fun D c _ V E c' _ L hL ↦ ?_) F hF
  have : TopologicalSpace.NoetherianSpace D := c.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace E := c'.isClosedEmbedding.isInducing.noetherianSpace
  obtain ⟨U, hU, rfl⟩ : ∃ U : X.Opens, (U : Set X)ᶜ ⊆ Set.range c.base ∧ c ⁻¹ᵁ U = V := by
    refine ⟨⟨(c.base '' (V : Set D)ᶜ)ᶜ,
      (c.isClosedEmbedding.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
    · rw [TopologicalSpace.Opens.coe_mk, compl_compl]
      exact Set.image_subset_range _ _
    · ext x
      simp [c.isClosedEmbedding.injective.mem_set_image]
  exact hiso (rightDerivedLowerStarOpenImmersionLowerShriekSingleIso _ c U hU c' L).symm
    (hgen' U.ι (c' ≫ c ∣_ U) L
      (isLocallyFree_of_isLocallyFinitelyPresented_of_noetherianSpace ℓ E hL))

end CondensedRing

open CondensedRing

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The generators `a_! L = j_! Ri_* L` descend to finite subextensions, for a locally closed
immersion `a = j ∘ i : S ⟶ U ⟶ X` into a scheme with noetherian underlying space and a lisse
`ℚ̄_ℓ,S`-module `L`. See the module docstring. -/
theorem descendsToPadicSubfield_lowerShriek [TopologicalSpace.NoetherianSpace X]
    {U S : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (i : S ⟶ U) [IsClosedImmersion i]
    (L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (padicAlgClRingObj S ℓ))
    (hL : IsLocallyFree (padicAlgClRingObj S ℓ) L) :
    descendsToPadicSubfield X ℓ ((D((j)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      ((R((i)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj L))) := by
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace S := i.isClosedEmbedding.isInducing.noetherianSpace
  obtain ⟨E, L', hL', ⟨e⟩⟩ := exists_isLocallyFree_extendScalars_iso ℓ S L hL
  refine ⟨E, (D((j)_!open⟦_⟧)).obj ((R((i)_*⟦_⟧)).obj
    ((DerivedCategory.singleFunctor _ 0).obj L')), ?_, ⟨?_⟩⟩
  · exact boundedConstructible_openImmersionLowerShriek_obj_of_noetherianSpace _ j
      (boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion _ i
        (boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject _ 0
          hL'.isConstructibleModuleObject))
  · exact derivedExtendScalarsLowerShriekSingleIso
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) j i L' ≪≫
      (D((j)_!open⟦_⟧)).mapIso ((R((i)_*⟦_⟧)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso e))

end AlgebraicGeometry.ProEtale
