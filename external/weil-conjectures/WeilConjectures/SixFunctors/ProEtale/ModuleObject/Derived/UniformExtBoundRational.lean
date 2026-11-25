/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralAcyclic
public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive

/-!
# Helpers for the uniform `Ext` bound for constructible `E`-sheaves, from `𝒪_E`

Blueprint `lemma-uniform-ext-bound`, coefficients `E`. Let `E ⊆ ℚ̄_ℓ` be a finite
subextension of `ℚ_ℓ` and `X` a scheme. This file computes `Ext` between extensions of scalars
`E ⊗_{𝒪_E} M₀` of `𝒪_{E,X}`-modules: by adjunction
`Ext^q_E(E ⊗ M₀, E ⊗ B₀) = Ext^q_{𝒪_E}(M₀, E ⊗ B₀)`, and `E ⊗ B₀` is the filtered colimit of
`B₀ --ℓ--> B₀ --ℓ--> ⋯` (`ProEtale.isColimitPadicIntegersRingObjSmulSequenceCocone`), so every
class factors through some `Ext^q_{𝒪_E}(M₀, B₀)`
(`ProEtale.eq_zero_of_extendScalars_padicIntegersToPadicSubfield`). The uniform bound itself is
deduced in `...Derived.UniformExtBoundRationalLattice`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

/-- A morphism `F X ⟶ Y` whose adjunct `X ⟶ G Y` vanishes vanishes. -/
lemma eq_zero_of_homEquiv_eq_zero {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {Y : D}
    {f : F.obj X ⟶ Y} (h : adj.homEquiv X Y f = 0) : f = 0 := by
  have : F.IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  rw [← (adj.homEquiv X Y).symm_apply_apply f, h, homEquiv_counit, F.map_zero, zero_comp]

end CategoryTheory.Adjunction

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] {φ : R ⟶ S} [IsMonHom φ] {n : ℕ}
  {c : ℕ → (R ⟶ S)}

omit [Preadditive C] [MonoidalPreadditive C] in
/-- The cocone map `e_0 : M ⟶ S ⊗_R M` is the unit of extension of scalars when `c_0 = φ`. -/
lemma extendScalarsCoconeι_zero (h0 : c 0 = φ) (M : Mod C R) :
    extendScalarsCoconeι φ c M 0 = extendUnitHom φ M := by
  rw [extendScalarsCoconeι, extendUnitHom, h0, IsMonHom.one_hom]

/-- If `c_0 = φ` and multiplication by `n` on `S ⊗_R M` is a monomorphism, the cocone maps
`e_k : M ⟶ S ⊗_R M` are `R`-linear: `n^k e_k = e_0` is the unit of extension of scalars. -/
lemma smul_extendScalarsCoconeι (hc : ∀ k, n • c (k + 1) = c k) (h0 : c 0 = φ) (M : Mod C R)
    [Mono (n • 𝟙 (extendScalarsObj φ M).X)] (k : ℕ) :
    γ[R,M.X] ≫ extendScalarsCoconeι φ c M k =
      R ◁ extendScalarsCoconeι φ c M k ≫ φ ▷ (extendScalarsObj φ M).X ≫
        γ[S,(extendScalarsObj φ M).X] := by
  induction k with
  | zero =>
    rw [extendScalarsCoconeι_zero h0]
    exact IsModHom.smul_hom (f := (extendUnit φ M).hom)
  | succ k ih =>
    rw [← cancel_mono (n • 𝟙 (extendScalarsObj φ M).X)]
    simp only [Preadditive.comp_nsmul, Category.comp_id]
    rw [← Preadditive.comp_nsmul, nsmul_extendScalarsCoconeι_succ φ hc, ih,
      ← Preadditive.nsmul_comp, ← MonoidalCategory.whiskerLeft_nsmul,
      nsmul_extendScalarsCoconeι_succ φ hc]

/-- The cocone map `e_k : M ⟶ S ⊗_R M` as a morphism of `R`-module objects, when `c_0 = φ` and
`S ⊗_R M = colim(M --n--> M --n--> ⋯)` along the `e_k`. -/
noncomputable def extendScalarsCoconeHom (hc : ∀ k, n • c (k + 1) = c k) (h0 : c 0 = φ)
    {M : Mod C R} (hM : IsColimit (extendScalarsCocone φ hc M)) (k : ℕ) :
    M ⟶ (comap φ).obj ((extendScalars φ).obj M) :=
  have := mono_nsmul_id_of_isColimit _ hM
  Hom.mk' (extendScalarsCoconeι φ c M k) (smul_extendScalarsCoconeι hc h0 M k)

@[simp]
lemma extendScalarsCoconeHom_hom (hc : ∀ k, n • c (k + 1) = c k) (h0 : c 0 = φ)
    {M : Mod C R} (hM : IsColimit (extendScalarsCocone φ hc M)) (k : ℕ) :
    (extendScalarsCoconeHom hc h0 hM k).hom = extendScalarsCoconeι φ c M k :=
  rfl

/-- The cocone `(e_k)_k : (M --n--> M --n--> ⋯) ⟶ S ⊗_R M` in `R`-module objects. -/
noncomputable abbrev extendScalarsModCocone (hc : ∀ k, n • c (k + 1) = c k) (h0 : c 0 = φ)
    {M : Mod C R} (hM : IsColimit (extendScalarsCocone φ hc M)) :
    Cocone (smulSequence M n) :=
  smulSequenceCocone n (extendScalarsCoconeHom hc h0 hM) fun k ↦
    Mod.hom_ext _ _ (nsmul_extendScalarsCoconeι_succ φ hc M k)

/-- **`S ⊗_R M = colim(M --n--> M --n--> ⋯)` in `R`-module objects**: the colimit
`isColimitExtendScalarsCocone` of underlying objects lifts to `R`-module objects. -/
noncomputable def isColimitExtendScalarsModCocone (hc : ∀ k, n • c (k + 1) = c k)
    (h0 : c 0 = φ) {M : Mod C R} (hM : IsColimit (extendScalarsCocone φ hc M))
    [ReflectsColimitsOfShape ℕ (forget (D := C) R)] :
    IsColimit (extendScalarsModCocone hc h0 hM) :=
  isColimitOfReflects (forget R)
    (((IsColimit.precomposeHomEquiv (smulSequenceCompIso (forget R) M n) _).symm hM).ofIsoColimit
      (Cocone.ext (Iso.refl _) fun k ↦ by simp [smulSequenceCompIso]))

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- `p_X^*(ℓ⁻⁰ φ) = φ`. -/
lemma padicIntegersToPadicSubfieldInvPow_zero (X : Scheme.{u}) :
    padicIntegersToPadicSubfieldInvPow ℓ E X 0 = padicIntegersToPadicSubfield X ℓ E :=
  congrArg (upperStarFromPoint X).map
    (Profinite.padicIntegersRingObjToContinuousMapRingObjInvPow_zero ℓ E)

/-- **`Ext` into `E ⊗ B₀` vanishes in the range of the uniform bound**: if morphisms out of `s`
factor through filtered colimits and `Hom(s, B[n])` vanishes for constructible
`𝒪_{E,X}`-modules `B` and `n ≤ N`, then so does `Hom(s, (E ⊗_{𝒪_E} B₀)[n])` for constructible
`B₀`, the restriction of scalars of `E ⊗_{𝒪_E} B₀` being the filtered colimit of
`B₀ --ℓ--> B₀ --ℓ--> ⋯` (`ProEtale.isColimitPadicIntegersExtendScalarsCocone`). -/
lemma eq_zero_of_comap_extendScalars_padicIntegersToPadicSubfield {X : Scheme.{u}}
    {s : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X))}
    (hc : DerivedCategory.HomFactorsThroughFilteredColimits.{u + 1} s) (N : ℤ)
    (hb : ∀ B, IsConstructibleModuleObject _ B → ∀ n ≤ N,
      ∀ f : s ⟶ (DerivedCategory.singleFunctor _ n).obj B, f = 0)
    (B₀ : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X))
    (hB₀ : IsConstructibleModuleObject _ B₀) (n : ℤ) (hn : n ≤ N)
    (g : s ⟶ (DerivedCategory.singleFunctor _ n).obj
      ((Mod.comap (padicIntegersToPadicSubfield X ℓ E)).obj
      ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj B₀))) :
    g = 0 := by
  let hB := Mod.isColimitExtendScalarsModCocone _ (padicIntegersToPadicSubfieldInvPow_zero ℓ E X)
    (isColimitPadicIntegersExtendScalarsCocone ℓ E X B₀)
  obtain ⟨i, g', rfl⟩ := hc (AsSmall.{u + 1} ℕ) _ _ (hB.whiskerEquivalence AsSmall.equiv.symm) n g
  rw [hb _ hB₀ n hn g', zero_comp]

/-- `E ⊗ᴸ_{𝒪_E} M₀[0] ≅ (E ⊗_{𝒪_E} M₀)[0]`, the extension of scalars being exact. -/
noncomputable def leftDerivedExtendScalarsSingleFunctorIso {X : Scheme.{u}}
    (M₀ : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)) :
    (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M₀) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj M₀) :=
  (Functor.singleFunctorCompLeftDerivedFunctorIso _).app M₀

/-- **`Ext^n_E(E ⊗ M₀, E ⊗ B₀) = 0` in the range of the uniform bound over `𝒪_E`**: by adjunction
`Ext^n_E(E ⊗ M₀, E ⊗ B₀) = Ext^n_{𝒪_E}(M₀, E ⊗ B₀)`, which vanishes by
`ProEtale.eq_zero_of_comap_extendScalars_padicIntegersToPadicSubfield`. -/
lemma eq_zero_of_extendScalars_padicIntegersToPadicSubfield {X : Scheme.{u}}
    {M₀ : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)}
    (hc : DerivedCategory.HomFactorsThroughFilteredColimits.{u + 1}
      ((DerivedCategory.singleFunctor _ 0).obj M₀)) (N : ℤ)
    (hb : ∀ B, IsConstructibleModuleObject _ B → ∀ n ≤ N,
      ∀ f : (DerivedCategory.singleFunctor _ 0).obj M₀ ⟶ (DerivedCategory.singleFunctor _ n).obj B,
        f = 0)
    (B₀ : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X))
    (hB₀ : IsConstructibleModuleObject _ B₀) (n : ℤ) (hn : n ≤ N)
    (f : (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj M₀) ⟶
      (DerivedCategory.singleFunctor _ n).obj
        ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj B₀)) :
    f = 0 := by
  have adj := Mod.derivedExtendMapDerivedCategoryAdjunction (padicIntegersToPadicSubfield X ℓ E)
  have e := ((Mod.comap (padicIntegersToPadicSubfield X ℓ E)).mapDerivedCategorySingleFunctor n).app
    ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj B₀)
  let f' : (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M₀) ⟶ (DerivedCategory.singleFunctor _ n).obj
        ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).obj B₀) :=
    (leftDerivedExtendScalarsSingleFunctorIso ℓ E M₀).hom ≫ f
  have h : adj.homEquiv _ _ f' = 0 := (cancel_mono e.hom).1
    ((eq_zero_of_comap_extendScalars_padicIntegersToPadicSubfield
      ℓ E hc N hb B₀ hB₀ n hn (adj.homEquiv _ _ f' ≫ e.hom)).trans zero_comp.symm)
  exact (cancel_epi (leftDerivedExtendScalarsSingleFunctorIso ℓ E M₀).hom).1
    ((adj.eq_zero_of_homEquiv_eq_zero h).trans comp_zero.symm)

end AlgebraicGeometry.ProEtale
