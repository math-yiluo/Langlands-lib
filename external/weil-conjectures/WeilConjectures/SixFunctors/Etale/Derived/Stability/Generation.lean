/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Generation of `Dctf`

This file computes the Tor amplitude of a flat sheaf placed in degree `0`, shows that
`Dctf(X, Λ)` is a thick subcategory of `D(X_ét, Λ)` for a finite ring `Λ`, and proves that it is
generated, as a thick subcategory, by the objects `Rg_* Rj_! L` for lisse flat sheaves `L` on the
strata of stratifications of `X`
(`ctf_generated_by_rightDerivedLowerStar_openImmersionLowerShriek`). Over a finite-type scheme
over a field, `Dctf(X, Λ)` is exactly the thick envelope of these generators
(`constructibleFiniteTor_eq_triangEnvelope_ctfGenerators`).

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-! ### Tor amplitude of a flat sheaf -/

section FlatSheaf

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}

/-- Tor amplitude in the sense of `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`,
tested on one homology sheaf at a time, is Tor amplitude in the sense of
`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn`, tested through the canonical
t-structure. -/
lemma torAmplitudeIn_of_hasTorAmplitudeIn {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : DerivedCategory.hasTorAmplitudeIn Λ X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K := fun F ↦ by
  rw [_root_.DerivedCategory.homologyConcentratedIn_iff]
  exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 fun q hq ↦ h F q (.inl hq),
    (_root_.DerivedCategory.isLE_iff _ b).2 fun q hq ↦ h F q (.inr hq)⟩

/-- A flat constructible sheaf placed in degree `0` has Tor amplitude in `[0, 0]`: the single
complex is its own bounded flat model
(`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`). -/
theorem torAmplitudeIn_singleFunctor_obj_of_flat
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (hF : ObjectProperty.flat F) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
  refine torAmplitudeIn_of_hasTorAmplitudeIn Λ ((hasTorAmplitudeIn_iff_exists_flatModel Λ 0 0
    le_rfl _ (DerivedCategory.boundedConstructible_singleFunctor_obj F 0)).2
    ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F, ⟨fun q hq ↦ ?_, fun q ↦ ?_⟩,
      ⟨(_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app F⟩⟩)
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · by_cases hq : q = 0
    · subst hq
      exact ObjectProperty.prop_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 F).symm hF
    · exact ObjectProperty.flat_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

end FlatSheaf

/-! ### `Dctf` is a thick subcategory -/

section Thick

variable (X : Scheme.{u})

/-- Finite Tor amplitude is a triangulated property of objects of `D(X_ét)`: the derived
tensor product `- ⊗ᴸ F` is a triangulated functor, and concentration in an interval is stable
under shifts and under extensions, with the interval shifted and widened. -/
instance DerivedCategory.finiteTorAmplitude_isTriangulated :
    (DerivedCategory.finiteTorAmplitude A X).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, 0, 0, fun F ↦ by
    have h : IsZero ((0 : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) ⊗
        (_root_.DerivedCategory.singleFunctor _ 0).obj F) :=
      Functor.map_isZero ((-⊗ᴸ-(X)[A]).flip.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) (isZero_zero _)
    exact ⟨(_root_.DerivedCategory.isGE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ h,
      (_root_.DerivedCategory.isLE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ h⟩⟩
  isStableUnderShiftBy n := ⟨fun M ⟨a, b, h⟩ ↦ ⟨a - n, b - n, fun F ↦ by
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    obtain ⟨h₁, h₂⟩ := h F
    let e := (((-⊗ᴸ-(X)[A]).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).commShiftIso n).app M
    have hge := _root_.DerivedCategory.TStructure.t.isGE_shift (M ⊗
      (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F) a n (a - n)
    have hle := _root_.DerivedCategory.TStructure.t.isLE_shift (M ⊗
      (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F) b n (b - n)
    exact ⟨@Triangulated.TStructure.isGE_of_iso _ _ _ _ _ _ _ _root_.DerivedCategory.TStructure.t
        _ _ e.symm (a - n) hge,
      @Triangulated.TStructure.isLE_of_iso _ _ _ _ _ _ _ _root_.DerivedCategory.TStructure.t
        _ _ e.symm (b - n) hle⟩⟩⟩
  ext₂' T hT := by
    rintro ⟨a, b, h₁⟩ ⟨c, d, h₃⟩
    refine ObjectProperty.le_isoClosure _ _ ⟨min a c, max b d, fun F ↦ ?_⟩
    let G := (-⊗ᴸ-(X)[A]).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    obtain ⟨g₁, l₁⟩ := (h₁ F).mono (min_le_left a c) (le_max_left b d)
    obtain ⟨g₃, l₃⟩ := (h₃ F).mono (min_le_right a c) (le_max_right b d)
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ (G.map_distinguished _ hT) _ g₁ g₃,
      _root_.DerivedCategory.TStructure.t.isLE₂ _ (G.map_distinguished _ hT) _ l₁ l₃⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- `Dctf(X, Λ)` is a triangulated subcategory of `D(X_ét, Λ)`, for a finite ring `Λ`. -/
instance DerivedCategory.constructibleFiniteTor_isTriangulated :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
  inferInstanceAs (boundedConstructible (ModuleCat.{u + 1} Λ) X ⊓
    DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) X).IsTriangulated

/-- `Dctf(X, Λ)` is stable under retracts, for a finite ring `Λ`. Together with
`DerivedCategory.constructibleFiniteTor_isTriangulated`, it is a thick subcategory of
`D(X_ét, Λ)`. -/
instance DerivedCategory.constructibleFiniteTor_isStableUnderRetracts :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).IsStableUnderRetracts where
  of_retract e h := ⟨(boundedConstructible _ X).prop_of_retract e h.1,
    (DerivedCategory.finiteTorAmplitude _ X).prop_of_retract e h.2⟩

end Thick


/-! ### Generation of `Dctf` -/

section Generation

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
variable {Λ} in
/-- Tor amplitude through the canonical t-structure gives Tor amplitude tested on one homology
sheaf at a time. -/
lemma hasTorAmplitudeIn_of_torAmplitudeIn {X : Scheme.{u}} {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K := fun F q hq ↦ by
  obtain ⟨h₁, h₂⟩ := h F
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 h₁ q hq
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 h₂ q hq

omit [Finite Λ] in
/-- The dévissage step of the generation statement: a thick
subcategory containing the generators `Rg_* j_! L` (`j_!` the extension by zero) contains
`Rι_* F` for every flat constructible sheaf `F` on a closed subscheme `ι : Z ⟶ X`. By
Noetherian induction on the support `T = ι(Z)`: `F` is lisse on a dense open `V ⊆ Z`, and the
open–closed triangle `j_! j^* F ⟶ F ⟶ i_* i^* F` for `V` and its closed complement exhibits
`Rι_* F` as an extension of a generator and of the direct image of the flat constructible sheaf
`i^* F` from a closed subscheme with smaller support. -/
theorem prop_rightDerivedLowerStar_of_flat (X : Scheme.{u}) [IsNoetherian X]
    (P : ObjectProperty
      (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (str : Scheme.Stratification X) (i : Fin str.n) (Ubar : Scheme.{u})
      (j : str.domain i ⟶ Ubar) [IsOpenImmersion j]
      (g : Ubar ⟶ X) [IsClosedImmersion g], Set.range (j ≫ g) = str.stratum i →
      Set.range g = _root_.closure (str.stratum i) →
      ∀ (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [IsFiniteLocallyConstantSheaf L], ObjectProperty.flat L →
        P ((R((g)_*[ModuleCat.{u + 1} Λ])).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L)))) :
    ∀ (T : TopologicalSpace.Closeds X) {Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι],
      Set.range ι.base = T → ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [IsConstructibleSheaf F], ObjectProperty.flat F →
        P ((R((ι)_*[ModuleCat.{u + 1} Λ])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  intro T
  induction T using WellFoundedLT.induction with
  | ind T ih =>
  intro Z ι _ hT F _ hF
  by_cases hZ : IsEmpty Z
  · exact P.prop_of_isZero (Functor.map_isZero _ (isZero_derivedCategory_of_isEmpty _ Z _))
  rw [not_isEmpty_iff] at hZ
  obtain ⟨V, hVd, hV⟩ := IsConstructibleSheaf.exists_dense_open F
  have : TopologicalSpace.NoetherianSpace Z := ι.isClosedEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) V.ι V.closedComplement
    (by simp) ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
  refine P.ext_of_isTriangulatedClosed₂ _ ((R((ι)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hw)
    ?_ ?_
  · -- the open part is a generator
    let str := Scheme.Stratification.ofClosedImmersionOpens ι V
    have := hP str (show Fin str.n from (1 : Fin 3)) Z
      (V.ι : str.domain (show Fin str.n from (1 : Fin 3)) ⟶ Z) ι (by simp [str,
      Scheme.Stratification.ofClosedImmersionOpens, Set.range_comp]) (by
        change Set.range ι.base = closure (ι.base '' V)
        rw [ι.isClosedEmbedding.closure_image_eq, hVd.closure_eq, Set.image_univ])
      ((V.ι)^*[_].obj F) (Functor.PreservesFlat.flat_obj (F := (V.ι)^*[_]) hF)
    exact P.prop_of_iso ((R((ι)_*[ModuleCat.{u + 1} Λ])).mapIso
      (D((V.ι)_!open[ModuleCat.{u + 1} Λ]).mapIso
        ((((V.ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F).symm)) this
  · -- the closed part is handled by induction
    have hlt : (⟨Set.range (V.closedComplement ≫ ι).base,
        (V.closedComplement ≫ ι).isClosedEmbedding.isClosed_range⟩ :
          TopologicalSpace.Closeds X) < T := by
      rw [← SetLike.coe_ssubset_coe, TopologicalSpace.Closeds.coe_mk, ← hT, Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.range_comp]
      refine (Set.image_subset_range _ _).ssubset_of_ne fun h ↦ ?_
      obtain ⟨z, hz⟩ := hVd.nonempty
      obtain ⟨y, hy, hyz⟩ : ι.base z ∈ ι.base '' Set.range V.closedComplement.base :=
        h ▸ ⟨z, rfl⟩
      rw [ι.isClosedEmbedding.injective hyz, V.range_closedComplement] at hy
      exact hy hz
    have : IsConstructibleSheaf ((V.closedComplement)^*[ModuleCat.{u + 1} Λ].obj F) :=
      IsConstructibleSheaf.upperStar _ _
    exact P.prop_of_iso (((rightDerivedLowerStarComp _ V.closedComplement ι).app _).symm ≪≫
      (R((ι)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((R((V.closedComplement)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((((V.closedComplement)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app
          F).symm))
      (ih _ hlt (V.closedComplement ≫ ι) rfl _
        (Functor.PreservesFlat.flat_obj (F := (V.closedComplement)^*[_]) hF))

/-- **Generation of `Dctf` over a Noetherian base.**

Let `X` be a Noetherian scheme and `Λ` a finite ring. Then `Dctf(X, Λ)` is generated as a
thick subcategory by the objects `Rg_* j_! L`, where `U` is a stratum of a stratification of
`X`, `j : U ⟶ Ū` is the open immersion of `U` into its closure, `j_!` is the (exact) extension
by zero along `j`, `g : Ū ⟶ X` is the closed immersion of that closure, and `L` is a lisse
(finite locally constant) flat sheaf of `Λ`-modules on `U`. Note the order: lower-star outside
lower-shriek. Here `a_! L = g_* j_! L` is the plain extension by zero along the
locally closed immersion `a = j ≫ g`; no compactification of `j` enters.

"Thick subcategory generated by" is unwound here: any property `P` of objects of `D(X_ét, Λ)`
that is triangulated, stable under retracts and closed under isomorphisms, and that holds for
all the generators above, holds for every object of `Dctf(X, Λ)`.

The lisse coefficients cannot be replaced by constant ones `Λ_U`: for `X = 𝔾_m`, `p ≠ 2` and
`Λ = 𝔽₃`, the complexes whose generic-stalk cohomology has only trivial `π₁`-composition factors
form a thick subcategory containing every `Rg_* Rj_! Λ_U` but not the order-`2` Kummer sheaf.

The proof resolves `K` by a bounded complex of flat constructible sheaves
(`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel`), reduces to one
flat constructible sheaf `F` by the stupid-truncation triangles, and then uses the open–closed
sequence `0 ⟶ j_!(F|_U) ⟶ F ⟶ i_* i^* F ⟶ 0` for a dense open `U` on which `F` is lisse,
together with Noetherian induction on the closed subsets of `X`. -/
theorem ctf_generated_by_rightDerivedLowerStar_openImmersionLowerShriek (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] (X : Scheme.{u}) [IsNoetherian X]
    (P : ObjectProperty
      (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    [P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (str : Scheme.Stratification X) (i : Fin str.n) (Ubar : Scheme.{u})
      (j : str.domain i ⟶ Ubar) [IsOpenImmersion j]
      (g : Ubar ⟶ X) [IsClosedImmersion g], Set.range (j ≫ g) = str.stratum i →
      Set.range g = _root_.closure (str.stratum i) →
      ∀ (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [IsFiniteLocallyConstantSheaf L], ObjectProperty.flat L →
        P ((R((g)_*[ModuleCat.{u + 1} Λ])).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    P K :=
  by
  obtain ⟨a, b, ⟨⟨hbc, hab⟩, hta⟩⟩ :=
    (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K).2 hK
  by_cases hab' : a ≤ b
  swap
  · have : K.IsGE a := hab.1
    have : K.IsLE b := hab.2
    exact P.prop_of_isZero (_root_.DerivedCategory.TStructure.t.isZero K b a (by omega))
  -- a bounded model by flat constructible sheaves, reduced to its terms by dévissage
  obtain ⟨Pc, ⟨hPz, hPflat⟩, hPc, ⟨e⟩⟩ := (hasTorAmplitudeIn_iff_exists_flatConstructibleModel
    Λ a b hab' K hbc).1 (hasTorAmplitudeIn_of_torAmplitudeIn hta)
  have : Pc.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hPz i (.inl hi)
  have : Pc.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hPz i (.inr hi)
  have hS := HomotopyCategory.mem_subcategory_of_strictly_bounded
    (P.inverseImage _root_.DerivedCategory.Qh) Pc a b (fun n _ _ ↦ ?_)
  · exact P.prop_of_iso e.symm (P.prop_of_iso
      ((_root_.DerivedCategory.quotientCompQhIso _).app Pc) hS)
  have := hPc n
  exact P.prop_of_iso ((rightDerivedLowerStarIdIso Λ X).app _)
    (prop_rightDerivedLowerStar_of_flat Λ X P hP ⊤ (𝟙 X) (by simp) (Pc.X n) (hPflat n))

/-- The generation statement with the generators written `Rg_* Rj_! L` through the derived
lower shriek of a compactification of `j` (the form used by the dévissage of `RHom` and of the
derived Hom amplitude); it follows from
`ctf_generated_by_rightDerivedLowerStar_openImmersionLowerShriek` since `Rj_! ≅ j_!` for a
quasi-compact open immersion `j` (`rightDerivedLowerShriekIsoOfIsOpenImmersion`). -/
theorem ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] (X : Scheme.{u}) [IsNoetherian X]
    (P : ObjectProperty
      (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    [P.IsTriangulated] [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (str : Scheme.Stratification X) (i : Fin str.n) (Ubar : Scheme.{u})
      (j : str.domain i ⟶ Ubar) [IsOpenImmersion j] [HasCompactification j]
      (g : Ubar ⟶ X) [IsClosedImmersion g], Set.range (j ≫ g) = str.stratum i →
      Set.range g = _root_.closure (str.stratum i) →
      ∀ (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} Λ))
        [IsFiniteLocallyConstantSheaf L], ObjectProperty.flat L →
        P ((R((g)_*[ModuleCat.{u + 1} Λ])).obj ((R(j)_![ModuleCat.{u + 1} Λ]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    P K := by
  refine ctf_generated_by_rightDerivedLowerStar_openImmersionLowerShriek Λ X P
    (fun str i Ubar j _ g _ h₁ h₂ L _ hL ↦ ?_) K hK
  have : TopologicalSpace.NoetherianSpace (str.domain i) :=
    (str.immersion i).isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification j := (Compactification.ofIsOpenImmersion j).hasCompactification
  exact P.prop_of_iso ((R((g)_*[ModuleCat.{u + 1} Λ])).mapIso
    ((rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).app _)) (hP str i Ubar j g h₁ h₂ L hL)

/-- The generators of `Dctf(X, Λ)`: the objects isomorphic to `Rg_* j_! L`, where `U` is a
stratum of a stratification of `X`, `j : U ⟶ Ū` is an open immersion, `j_!` the extension by zero
along `j`, and `g : Ū ⟶ X` a closed immersion with image the closure of `U`, and `L` is a lisse
(finite locally constant) flat sheaf of `Λ`-modules on `U`, placed in degree `0`. These are the
`a_! L` for `a = j ≫ g` the locally closed immersion of the stratum. -/
def ctfGenerators (X : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∃ (str : Scheme.Stratification X) (i : Fin str.n) (Ubar : Scheme.{u})
    (j : str.domain i ⟶ Ubar) (_ : IsOpenImmersion j)
    (g : Ubar ⟶ X) (_ : IsClosedImmersion g), Set.range (j ≫ g) = str.stratum i ∧
    Set.range g = _root_.closure (str.stratum i) ∧
    ∃ (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsFiniteLocallyConstantSheaf L ∧ ObjectProperty.flat L ∧
      Nonempty (K ≅ (R((g)_*[ModuleCat.{u + 1} Λ])).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)))

omit [Finite Λ] in
/-- The zero object is a generator, for the trivial stratification and `L = 0`. -/
instance (X : Scheme.{u}) : (ctfGenerators Λ X).Nonempty :=
  ⟨_, Stratification.trivial X, (0 : Fin 1), X, 𝟙 X,
    (inferInstance : IsOpenImmersion (𝟙 X)), 𝟙 X,
    inferInstance, Set.range_eq_univ.2 fun x ↦ ⟨x, rfl⟩, by simp, 0,
    IsFiniteLocallyConstantSheaf.of_isZero (isZero_zero _),
    ObjectProperty.flat_of_isZero (isZero_zero _), ⟨Iso.refl _⟩⟩

/-- The direct image along a closed immersion `g : Z ⟶ X` of finite-type `k`-schemes preserves
the constructible finite-Tor subcategories: `Rg_* = g_*` is exact, so it preserves bounded
constructibility, and the Tor amplitude of `Rg_* K` is bounded by that of `K` plus twice the
dimension of `Z`, by the projection formula with the residue field of `Λ`. -/
theorem constructibleFiniteTor_rightDerivedLowerStar_of_isClosedImmersion {k : Type u} [Field k]
    {Z X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (g : Z ⟶ X) [IsClosedImmersion g]
    {K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((R((g)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨hbc, a, b, hta⟩ := hK
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (g ≫ aX)
  exact ⟨boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion g hbc, a, b + 2 * (d : ℤ),
    torAmplitudeIn_rightDerivedLowerStar_of_finite Λ (g ≫ aX) aX g rfl d hd a b hta⟩

/-- **Constructible dévissage: the thick-subcategory generation of `Dctf`.**

Let `X` be a finite-type scheme over a field `k` and `Λ` a finite ring whose exponent is
invertible on `X`. Then `Dctf(X, Λ)` *is* the thick subcategory of `D(X_ét, Λ)` generated by the
objects `Rg_* j_! L` of `ctfGenerators` (`ObjectProperty.triangEnvelope`, the smallest
triangulated subcategory stable under retracts containing them).

The generators lie in `Dctf(X, Λ)`: a lisse flat sheaf has Tor amplitude `[0, 0]`
(`torAmplitudeIn_singleFunctor_obj_of_flat`), and the extension by zero `j_!` and `Rg_*`
preserve `Dctf`
(`boundedConstructible_and_torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek`,
`constructibleFiniteTor_rightDerivedLowerStar_of_isClosedImmersion`); and `Dctf(X, Λ)` is thick.
Conversely every object of `Dctf(X, Λ)` lies in the envelope by
`ctf_generated_by_rightDerivedLowerStar_openImmersionLowerShriek`. Constant coefficients
`L = Λ_U` do not suffice, see there. -/
theorem constructibleFiniteTor_eq_triangEnvelope_ctfGenerators {k : Type u} [Field k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent Λ X] :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X = (ctfGenerators Λ X).triangEnvelope := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  refine le_antisymm (fun K hK ↦ ?_) ((ObjectProperty.triangEnvelope_le_iff _).2 ?_)
  · refine ctf_generated_by_rightDerivedLowerStar_openImmersionLowerShriek Λ X _
      (fun str i Ubar j _ g _ h₁ h₂ L _ hL ↦ ?_) K hK
    exact ObjectProperty.le_triangEnvelope _ _
      ⟨str, i, Ubar, j, inferInstance, g, inferInstance, h₁, h₂, L, inferInstance, hL,
        ⟨Iso.refl _⟩⟩
  · rintro K ⟨str, i, Ubar, j, _, g, _, -, -, L, _, hL, ⟨e⟩⟩
    refine (constructibleFiniteTor _ X).prop_of_iso e.symm ?_
    have : HasInvertibleExponent Λ Ubar := .of_hom g
    have : TopologicalSpace.NoetherianSpace (str.domain i) :=
      (str.immersion i).isEmbedding.isInducing.noetherianSpace
    have : QuasiCompact j := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    have : IsConstructibleSheaf L := IsFiniteLocallyConstantSheaf.isConstructibleSheaf ‹_›
    have h := boundedConstructible_and_torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek
      Λ j (boundedConstructible_singleFunctor_obj L 0)
      ((_root_.DerivedCategory.homologyConcentratedIn_iff 0 0 _).2 ⟨inferInstance, inferInstance⟩)
      (torAmplitudeIn_singleFunctor_obj_of_flat Λ L hL)
    exact constructibleFiniteTor_rightDerivedLowerStar_of_isClosedImmersion Λ aX g
      ⟨h.1, 0, 0, h.2.2⟩


end Generation

end Etale

end AlgebraicGeometry
