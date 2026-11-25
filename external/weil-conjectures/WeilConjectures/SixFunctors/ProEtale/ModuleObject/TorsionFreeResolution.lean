/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-!
# Torsion-free acyclic resolutions

Let `D` be an abelian braided monoidal closed category, `r : 𝟙_ D ⟶ 𝟙_ D` an endomorphism of the
unit, acting on every object `M` by `r_M : M ⟶ M` (`MonoidalCategory.unitEndSMul`), and
`ι : 𝟙_ D ⟶ F` a morphism such that `r_F` is an epimorphism and `F` is flat. In the application,
`D` is the category of `𝒪_{E,X}`-modules, `r` is a uniformizer `ϖ` and `ι : 𝒪_{E,X} ⟶ E_X` is the
inclusion.

For a bounded below complex `I` of injective objects, we construct a complex `J`
(`CochainComplex.torsionFreeResolution`) quasi-isomorphic to `I`, whose terms are acted upon
injectively by `r` and are acyclic for every right adjoint `G` whose left adjoint `L` is exact
and such that every object is a quotient of an object `M` with `ι ▷ L M` a monomorphism.

## Construction

Let `B = [F, I]` and `I' = [𝟙, I] ≅ I`. Then

* `B` is injective, the internal hom out of the flat object `F` being right adjoint to an exact
  functor (`MonoidalClosed.injective_ihom_obj`);
* `r` acts on `B` through `[r_F, I]` (`MonoidalCategory.unitEndSMul_ihom`), which is a
  monomorphism as `r_F` is an epimorphism (`MonoidalClosed.mono_unitEndSMul_ihom`);
* `[ι, I] : B ⟶ I'` is an epimorphism, and stays one after applying `G`
  (`MonoidalClosed.epi_map_pre_app`): a map `M ⟶ [𝟙, I]` is a map `𝟙 ⊗ M ⟶ I`, which extends along
  the monomorphism `ι ▷ M` by injectivity of `I`.

So with `A = ker([ι, I])`, `0 ⟶ A ⟶ B ⟶ I' ⟶ 0` is a degreewise short exact sequence of
complexes, `r` acts injectively on `A ⊆ B`, and `A` is `G`-acyclic
(`ShortComplex.ShortExact.rightAcyclic_X₁`). The mapping cone `J` of `A ⟶ B` is quasi-isomorphic
to `I'`, and its terms `A^{k+1} ⊞ B^k` have the required properties.

Note that one cannot ask for the terms of `J` to be both injective and `r`-torsion-free in
general: over `𝒪_E`, `r = ϖ` acts surjectively on injective modules, so it would act invertibly
on the cohomology of `J`.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory MonoidalClosed

namespace MonoidalCategory

variable {D : Type*} [Category* D] [MonoidalCategory D] (r : 𝟙_ D ⟶ 𝟙_ D)

/-- The action `r_M : M ⟶ M` of an endomorphism `r` of the monoidal unit on an object `M`,
through the left unitor `𝟙 ⊗ M ≅ M`. -/
def unitEndSMul (M : D) : M ⟶ M :=
  (λ_ M).inv ≫ r ▷ M ≫ (λ_ M).hom

/-- `r_M` is natural in `M`. -/
@[reassoc]
lemma unitEndSMul_naturality {M N : D} (g : M ⟶ N) :
    unitEndSMul r M ≫ g = g ≫ unitEndSMul r N := by
  simp only [unitEndSMul, Category.assoc, ← leftUnitor_naturality, whisker_exchange_assoc,
    leftUnitor_inv_naturality_assoc]

/-- `r_M ⊗ N = r_{M ⊗ N}`. -/
lemma unitEndSMul_whiskerRight (M N : D) :
    unitEndSMul r M ▷ N = unitEndSMul r (M ⊗ N) := by
  simp only [unitEndSMul, comp_whiskerRight, leftUnitor_tensor_hom, leftUnitor_tensor_inv,
    Category.assoc, Iso.hom_inv_id_assoc, associator_inv_naturality_left_assoc]

/-- `M ⊗ r_N = r_{M ⊗ N}` in a braided monoidal category. -/
lemma unitEndSMul_whiskerLeft [BraidedCategory D] (M N : D) :
    M ◁ unitEndSMul r N = unitEndSMul r (M ⊗ N) := by
  rw [← cancel_mono (β_ M N).hom, BraidedCategory.braiding_naturality_right,
    unitEndSMul_whiskerRight, unitEndSMul_naturality]

/-- The action of `r` on an internal hom `[F, I]` is the precomposition with `r_F`. -/
lemma unitEndSMul_ihom [BraidedCategory D] [MonoidalClosed D] (F I : D) :
    unitEndSMul r ((ihom F).obj I) = (pre (unitEndSMul r F)).app I := by
  apply uncurry_injective
  rw [uncurry_pre, uncurry_eq, unitEndSMul_whiskerLeft,
    unitEndSMul_whiskerRight]

end MonoidalCategory

namespace MonoidalClosed

variable {D : Type*} [Category* D] [MonoidalCategory D] [MonoidalClosed D]

/-- If `r` acts on `F` by an epimorphism, it acts on `[F, I]` by a monomorphism. -/
lemma mono_unitEndSMul_ihom [BraidedCategory D] (r : 𝟙_ D ⟶ 𝟙_ D) (F I : D)
    [Epi (unitEndSMul r F)] :
    Mono (unitEndSMul r ((ihom F).obj I)) := by
  rw [unitEndSMul_ihom]
  exact mono_pre_app _ _

/-- The internal hom `[F, I]` from an object `F` such that `F ⊗ -` preserves monomorphisms into
an injective object `I` is injective. -/
lemma injective_ihom_obj (F I : D) [(tensorLeft F).PreservesMonomorphisms] [Injective I] :
    Injective ((ihom F).obj I) :=
  (ihom.adjunction F).map_injective _ inferInstance

variable {F : D} (ι : 𝟙_ D ⟶ F)

/-- For an injective `I`, a map `M ⟶ [𝟙, I]` lifts along `[ι, I] : [F, I] ⟶ [𝟙, I]` as soon as
`ι ▷ M : 𝟙 ⊗ M ⟶ F ⊗ M` is a monomorphism. -/
lemma exists_comp_pre_app_eq (I : D) [Injective I] {M : D} [Mono (ι ▷ M)]
    (g : M ⟶ (ihom (𝟙_ D)).obj I) : ∃ h : M ⟶ (ihom F).obj I, h ≫ (pre ι).app I = g :=
  ⟨curry (Injective.factorThru (uncurry g) (ι ▷ M)), by
    rw [curry_pre_app, Injective.comp_factorThru, curry_uncurry]⟩

/-- For an injective `I`, `G([ι, I]) : G[F, I] ⟶ G[𝟙, I]` is an epimorphism, for a right adjoint
`G` with left adjoint `L` such that every object is a quotient of an object `M` with `ι ▷ L M` a
monomorphism. -/
lemma epi_map_pre_app {D' : Type*} [Category* D'] {L : D' ⥤ D} {G : D ⥤ D'} (adj : L ⊣ G)
    (I : D) [Injective I]
    (h : ∀ Y : D', ∃ (M : D') (π : M ⟶ Y), Epi π ∧ Mono (ι ▷ L.obj M)) :
    Epi (G.map ((pre ι).app I)) := by
  obtain ⟨M, π, _, _⟩ := h (G.obj ((ihom (𝟙_ D)).obj I))
  obtain ⟨g, hg⟩ := exists_comp_pre_app_eq ι I ((adj.homEquiv _ _).symm π)
  refine epi_of_epi_fac (f := adj.homEquiv _ _ g) (h := π) ?_
  rw [← Adjunction.homEquiv_naturality_right, hg, Equiv.apply_symm_apply]

/-- For an injective `I`, `[ι, I] : [F, I] ⟶ [𝟙, I]` is an epimorphism if every object is a
quotient of an object `M` with `ι ▷ M` a monomorphism. -/
lemma epi_pre_app (I : D) [Injective I]
    (h : ∀ Y : D, ∃ (M : D) (π : M ⟶ Y), Epi π ∧ Mono (ι ▷ M)) :
    Epi ((pre ι).app I) :=
  epi_map_pre_app ι (L := 𝟭 D) (G := 𝟭 D) Adjunction.id I h

end MonoidalClosed

section Generators

variable {D : Type*} [Category* D] [MonoidalCategory D]

/-- If `D` has functorial flat resolutions and `ι` is a monomorphism, every object is a quotient
of a (flat) object `M` such that `ι ▷ M` is a monomorphism. -/
lemma exists_epi_mono_whiskerRight [Abelian D] [h : Abelian.HasFunctorialFlatResolution D]
    {A B : D} (ι : A ⟶ B) [Mono ι] (Y : D) :
    ∃ (M : D) (π : M ⟶ Y), Epi π ∧ Mono (ι ▷ M) := by
  let M : D := (h.some.F.obj Y).obj
  have hM : ObjectProperty.flat M := (h.some.F.obj Y).property
  have := hM.tensorRight.preservesFiniteLimits
  exact ⟨M, h.some.π.app Y, inferInstance, (tensorRight M).map_mono ι⟩

/-- Let `L : D' ⥤ D` be a monoidal functor preserving monomorphisms, and `ι' : 𝟙 ⟶ F'`,
`ι : 𝟙 ⟶ F` be compatible morphisms, `L F' ≅ F`. If `ι' ▷ M` is a monomorphism, so is
`ι ▷ L M`. -/
lemma mono_whiskerRight_obj {D' : Type*} [Category* D'] [MonoidalCategory D'] (L : D' ⥤ D)
    [L.Monoidal] [L.PreservesMonomorphisms] {F' : D'} (ι' : 𝟙_ D' ⟶ F') {F : D}
    (ι : 𝟙_ D ⟶ F) (e : L.obj F' ≅ F) (he : Functor.LaxMonoidal.ε L ≫ L.map ι' ≫ e.hom = ι)
    (M : D') [Mono (ι' ▷ M)] : Mono (ι ▷ L.obj M) := by
  have : Mono (L.map ι' ▷ L.obj M ≫ Functor.LaxMonoidal.μ L F' M) := by
    rw [Functor.LaxMonoidal.μ_natural_left]
    exact mono_comp _ (L.map (ι' ▷ M))
  have : Mono (L.map ι' ▷ L.obj M) := mono_of_mono _ (Functor.LaxMonoidal.μ L F' M)
  rw [← he, comp_whiskerRight, comp_whiskerRight]
  infer_instance

/-- Under the assumptions of `mono_whiskerRight_obj`, if `D'` has functorial flat resolutions and
`ι'` is a monomorphism, every object of `D'` is a quotient of an object `M` with `ι ▷ L M` a
monomorphism. -/
lemma exists_epi_mono_whiskerRight_obj {D' : Type*} [Category* D'] [MonoidalCategory D']
    [Abelian D'] [Abelian.HasFunctorialFlatResolution D'] (L : D' ⥤ D)
    [L.Monoidal] [L.PreservesMonomorphisms] {F' : D'} (ι' : 𝟙_ D' ⟶ F') [Mono ι'] {F : D}
    (ι : 𝟙_ D ⟶ F) (e : L.obj F' ≅ F) (he : Functor.LaxMonoidal.ε L ≫ L.map ι' ≫ e.hom = ι)
    (Y : D') : ∃ (M : D') (π : M ⟶ Y), Epi π ∧ Mono (ι ▷ L.obj M) := by
  obtain ⟨M, π, hπ, _⟩ := exists_epi_mono_whiskerRight ι' Y
  exact ⟨M, π, hπ, mono_whiskerRight_obj L ι' ι e he M⟩

end Generators

namespace ShortComplex.ShortExact

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D] {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] {S : ShortComplex C}

/-- `F`-acyclic objects are closed under kernels of epimorphisms which stay epimorphisms after
applying `F`: if `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is short exact, `B` and `C` are `F`-acyclic and
`F B ⟶ F C` is an epimorphism, then `A` is `F`-acyclic. -/
lemma rightAcyclic_X₁ (hS : S.ShortExact) (h₂ : F.rightAcyclic S.X₂)
    (h₃ : F.rightAcyclic S.X₃) [Epi (F.map S.g)] : F.rightAcyclic S.X₁ := by
  intro q
  obtain ⟨δ, w₁, w₂, -, h⟩ := hS.exists_rightDerived_δ_exact F q
  refine (h.isZero_X₂_iff).2 ⟨?_, (h₂ q).eq_of_tgt _ _⟩
  change δ = 0
  cases q with
  | zero =>
    have : Epi ((F.rightDerived 0).map S.g) := by
      rw [← NatIso.naturality_2 F.rightDerivedZeroIsoSelf S.g]
      infer_instance
    exact (cancel_epi ((F.rightDerived 0).map S.g)).1 (w₁.trans comp_zero.symm)
  | succ k => exact (h₃ k).eq_of_src _ _

end ShortComplex.ShortExact

namespace MonoidalCategory

variable {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D] [MonoidalCategory D]
  (r : 𝟙_ D ⟶ 𝟙_ D)

/-- `r` acts on a biproduct componentwise. -/
lemma unitEndSMul_biprod (X Y : D) :
    unitEndSMul r (X ⊞ Y) = biprod.map (unitEndSMul r X) (unitEndSMul r Y) := by
  apply biprod.hom_ext <;> simp [unitEndSMul_naturality]

end MonoidalCategory

end CategoryTheory

namespace CochainComplex

open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex

variable {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] {F : D} (ι : 𝟙_ D ⟶ F) (I : CochainComplex D ℤ)

/-- The map `[ι, I] : [F, I] ⟶ [𝟙, I]` of complexes. -/
noncomputable def torsionFreeResolutionπ :
    ((ihom F).mapHomologicalComplex (.up ℤ)).obj I ⟶
      ((ihom (𝟙_ D)).mapHomologicalComplex (.up ℤ)).obj I :=
  (NatTrans.mapHomologicalComplex (pre ι) _).app I

@[simp]
lemma torsionFreeResolutionπ_f (k : ℤ) :
    (torsionFreeResolutionπ ι I).f k = (pre ι).app (I.X k) := rfl

/-- The sequence `0 ⟶ A ⟶ [F, I] ⟶ [𝟙, I]`, `A` being the kernel of `[ι, I]`. -/
noncomputable def torsionFreeResolutionShortComplex : ShortComplex (CochainComplex D ℤ) :=
  ShortComplex.mk _ _ (kernel.condition (torsionFreeResolutionπ ι I))

/-- The mapping cone `J` of `A ⟶ [F, I]`, `A` being the kernel of `[ι, I] : [F, I] ⟶ [𝟙, I]`.
For a complex `I` of injective objects, it is a resolution of `I` by `r`-torsion-free acyclic
objects. -/
noncomputable def torsionFreeResolution : CochainComplex D ℤ :=
  mappingCone (torsionFreeResolutionShortComplex ι I).f

/-- The terms of `J` are `J^k = A^{k+1} ⊞ [F, I^k]`. -/
noncomputable def torsionFreeResolutionXIso (k : ℤ) :
    (torsionFreeResolution ι I).X k ≅
      (kernel (torsionFreeResolutionπ ι I)).X (k + 1) ⊞ (ihom F).obj (I.X k) :=
  homotopyCofiber.XIsoBiprod (torsionFreeResolutionShortComplex ι I).f k (k + 1) rfl

/-- The isomorphism of complexes `I ≅ [𝟙, I]`. -/
noncomputable def torsionFreeResolutionUnitIso :
    I ≅ ((ihom (𝟙_ D)).mapHomologicalComplex (.up ℤ)).obj I :=
  Hom.isoOfComponents (fun k ↦ unitNatIso.app (I.X k))
    (fun _ _ _ ↦ (unitNatIso.hom.naturality _).symm)

instance mono_kernel_ι_torsionFreeResolutionπ_f (k : ℤ) :
    Mono ((kernel.ι (torsionFreeResolutionπ ι I)).f k) :=
  inferInstanceAs (Mono ((eval D (.up ℤ) k).map (kernel.ι _)))

variable {ι I} (hI : ∀ k, Injective (I.X k))
  (hgen : ∀ Y : D, ∃ (M : D) (π : M ⟶ Y), Epi π ∧ Mono (ι ▷ M))

include hI hgen in
lemma epi_torsionFreeResolutionπ : Epi (torsionFreeResolutionπ ι I) :=
  epi_of_epi_f _ fun k ↦ by
    have := hI k
    exact epi_pre_app ι (I.X k) hgen

include hI hgen in
lemma shortExact_torsionFreeResolutionShortComplex :
    (torsionFreeResolutionShortComplex ι I).ShortExact := by
  have := epi_torsionFreeResolutionπ hI hgen
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    (inferInstanceAs (Mono (kernel.ι _))) this

variable (ι I)

/-- The quasi-isomorphism `J ⟶ I`. -/
noncomputable def torsionFreeResolutionHom : torsionFreeResolution ι I ⟶ I :=
  mappingCone.descShortComplex _ ≫ (torsionFreeResolutionUnitIso I).inv

include hI hgen in
lemma quasiIso_torsionFreeResolutionHom : QuasiIso (torsionFreeResolutionHom ι I) := by
  have := mappingCone.quasiIso_descShortComplex
    (shortExact_torsionFreeResolutionShortComplex hI hgen)
  dsimp [torsionFreeResolutionHom]
  infer_instance


/-- `J` lies in degrees `≥ n - 1` if `I` lies in degrees `≥ n`. -/
lemma isStrictlyGE_torsionFreeResolution (n : ℤ) [I.IsStrictlyGE n] :
    (torsionFreeResolution ι I).IsStrictlyGE (n - 1) := by
  refine (isStrictlyGE_iff _ _).2 fun k hk ↦ IsZero.of_iso ?_ (torsionFreeResolutionXIso ι I k)
  refine (biprod_isZero_iff _ _).2 ⟨?_, ?_⟩
  · refine IsZero.of_mono ((kernel.ι (torsionFreeResolutionπ ι I)).f (k + 1)) ?_
    exact Functor.map_isZero _ (I.isZero_of_isStrictlyGE n _ (by lia))
  · exact Functor.map_isZero _ (I.isZero_of_isStrictlyGE n _ (by lia))

variable [BraidedCategory D]

/-- `r` acts injectively on the terms of `J` if it acts on `F` by an epimorphism. -/
lemma mono_unitEndSMul_torsionFreeResolution_X (r : 𝟙_ D ⟶ 𝟙_ D) [Epi (unitEndSMul r F)]
    (k : ℤ) : Mono (unitEndSMul r ((torsionFreeResolution ι I).X k)) := by
  have hA : Mono (unitEndSMul r ((kernel (torsionFreeResolutionπ ι I)).X (k + 1))) := by
    have := mono_unitEndSMul_ihom r F (I.X (k + 1))
    have : Mono (unitEndSMul r ((kernel (torsionFreeResolutionπ ι I)).X (k + 1)) ≫
        (kernel.ι (torsionFreeResolutionπ ι I)).f (k + 1)) := by
      rw [unitEndSMul_naturality]
      exact mono_comp _ (unitEndSMul r ((ihom F).obj (I.X (k + 1))))
    exact mono_of_mono _ ((kernel.ι (torsionFreeResolutionπ ι I)).f (k + 1))
  have := mono_unitEndSMul_ihom r F (I.X k)
  rw [← Category.comp_id (unitEndSMul r _), ← (torsionFreeResolutionXIso ι I k).hom_inv_id,
    unitEndSMul_naturality_assoc, unitEndSMul_biprod]
  infer_instance

omit [BraidedCategory D] in
include hI hgen in
/-- The terms of `J` are `G`-acyclic, for a left exact right adjoint `G` whose left adjoint `L`
preserves monomorphisms and such that every object is a quotient of an object `M` with
`ι ▷ L M` a monomorphism, if `F ⊗ -` preserves monomorphisms. -/
lemma rightAcyclic_torsionFreeResolution_X [HasInjectiveResolutions D]
    [(tensorLeft F).PreservesMonomorphisms] {D' : Type*} [Category* D'] [Abelian D']
    {L : D' ⥤ D} {G : D ⥤ D'} [G.Additive] [PreservesFiniteLimits G] (adj : L ⊣ G)
    [L.PreservesMonomorphisms]
    (hL : ∀ Y : D', ∃ (M : D') (π : M ⟶ Y), Epi π ∧ Mono (ι ▷ L.obj M)) (k : ℤ) :
    G.rightAcyclic ((torsionFreeResolution ι I).X k) := by
  have := hI k
  have := hI (k + 1)
  have : Injective ((ihom F).obj (I.X k)) := injective_ihom_obj _ _
  refine G.rightAcyclic.prop_of_iso (torsionFreeResolutionXIso ι I k).symm
    (Functor.rightAcyclic_biprod ?_ (Functor.rightAcyclic_of_injective _))
  have hS := (shortExact_torsionFreeResolutionShortComplex hI hgen).map_of_exact
    (eval D (.up ℤ) (k + 1))
  have : Injective ((ihom F).obj (I.X (k + 1))) := injective_ihom_obj _ _
  have : Injective ((ihom (𝟙_ D)).obj (I.X (k + 1))) :=
    Injective.of_iso (unitNatIso.app (I.X (k + 1))) (hI (k + 1))
  have a₂ : G.rightAcyclic ((ihom F).obj (I.X (k + 1))) := Functor.rightAcyclic_of_injective _
  have a₃ : G.rightAcyclic ((ihom (𝟙_ D)).obj (I.X (k + 1))) :=
    Functor.rightAcyclic_of_injective _
  have : Epi (G.map (((torsionFreeResolutionShortComplex ι I).map
      (eval D (.up ℤ) (k + 1))).g)) := epi_map_pre_app ι adj _ hL
  exact hS.rightAcyclic_X₁ a₂ a₃

end CochainComplex

namespace DerivedCategory

open CategoryTheory Limits MonoidalCategory MonoidalClosed CochainComplex

variable {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [HasDerivedCategory D] [EnoughInjectives D] {F : D} (ι : 𝟙_ D ⟶ F)
  (hgen : ∀ Y : D, ∃ (M : D) (π : M ⟶ Y), Epi π ∧ Mono (ι ▷ M))

include hgen in
/-- Every bounded below object `K ≥ n` of the derived category is represented by
`torsionFreeResolution ι I` for a complex `I ≥ n` of injective objects. -/
theorem exists_iso_Q_obj_torsionFreeResolution (K : DerivedCategory D) (n : ℤ) [K.IsGE n] :
    ∃ (I : CochainComplex D ℤ) (_ : ∀ k, Injective (I.X k)) (_ : I.IsStrictlyGE n),
      Nonempty (K ≅ Q.obj (torsionFreeResolution ι I)) := by
  obtain ⟨T, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isGE n
  obtain ⟨I, i, _, hI, _⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective T n
  have := quasiIso_torsionFreeResolutionHom ι I hI hgen
  exact ⟨I, hI, inferInstance,
    ⟨e ≪≫ asIso (Q.map i) ≪≫ (asIso (Q.map (torsionFreeResolutionHom ι I))).symm⟩⟩

end DerivedCategory
