/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModelOfClass
public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Presentation
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
/-!
# Bounded flat models

Finite Tor amplitude in `[a, b]` is the same as admitting a bounded flat model concentrated in
`[a, b]` (`lemma-flat-models-generators`).

## Main definitions

- `AlgebraicGeometry.Etale.IsBoundedFlatComplex`

## Main statements

- `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`
- `AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
/-- A complex `P` of sheaves of `Λ`-modules on `X_ét` is a *bounded flat complex in degrees
`[a, b]`* if every `P^q` is flat and `P^q = 0` for `q ∉ [a, b]`. -/
def IsBoundedFlatComplex (a b : ℤ)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) : Prop :=
  (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧ ∀ q : ℤ, ObjectProperty.flat (P.X q)

variable {Λ} in
/-- Tor amplitude tested on one homology sheaf at a time
(`AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`) is Tor amplitude tested through
the canonical t-structure (`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn`). -/
lemma DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K ↔
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K := by
  refine ⟨fun h F ↦ ?_, fun h F q hq ↦ ?_⟩
  · rw [_root_.DerivedCategory.homologyConcentratedIn_iff]
    exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 fun q hq ↦ h F q (.inl hq),
      (_root_.DerivedCategory.isLE_iff _ b).2 fun q hq ↦ h F q (.inr hq)⟩
  · obtain ⟨h₁, h₂⟩ := h F
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff _ a).1 h₁ q hq
    · exact (_root_.DerivedCategory.isLE_iff _ b).1 h₂ q hq

variable {Λ} in
/-- A bounded flat complex in degrees `[a, b]` is a complex of flat sheaves strictly
concentrated in degrees `[a, b]`. -/
lemma isBoundedFlatComplex_iff {a b : ℤ}
    {P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ} :
    IsBoundedFlatComplex Λ a b P ↔
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ q : ℤ, ObjectProperty.flat (P.X q) := by
  rw [CochainComplex.isStrictlyGE_iff, CochainComplex.isStrictlyLE_iff]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun q hq ↦ h₁ q (.inl hq), fun q hq ↦ h₁ q (.inr hq), h₂⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨fun q hq ↦ ?_, h₃⟩⟩
  rcases hq with hq | hq
  · exact h₁ q hq
  · exact h₂ q hq

/-- Blueprint `lemma-flat-models-generators` (also `lemma-flat-models-generators--1`): Bounded flat
model of finite Tor amplitude

**Finite Tor amplitude means a bounded flat model.** For `K ∈ D^b_c(X, Λ)` and integers
`a ≤ b` the following are equivalent: `K` has Tor amplitude in `[a, b]`; and `K` is isomorphic
to a bounded flat complex `P` in degrees `[a, b]`.

One direction is that a bounded-above complex of flat sheaves is K-flat; the other truncates a
bounded-above free resolution and checks that the truncation is flat by the Tor criterion. -/
theorem hasTorAmplitudeIn_iff_exists_flatModel (a b : ℤ) (_hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        IsBoundedFlatComplex Λ a b P ∧ Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  rw [DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn]
  refine (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).trans
    ⟨fun ⟨P, h₁, h₂, h₃, ⟨e⟩⟩ ↦ ⟨P, isBoundedFlatComplex_iff.2 ⟨h₁, h₂, h₃⟩, ⟨e.symm⟩⟩,
    fun ⟨P, hP, ⟨e⟩⟩ ↦ ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := isBoundedFlatComplex_iff.1 hP
  exact ⟨P, h₁, h₂, h₃, ⟨e.symm⟩⟩

open ZeroObject in
/-- **Flat constructible sheaves lift along epimorphisms onto constructible sheaves.** Let `X`
be Noetherian and `Λ` finite. For every epimorphism `p : A ⟶ B` of sheaves of `Λ`-modules on
`X_ét` and every morphism `g : G ⟶ B` from a constructible sheaf `G`, there are a flat
constructible sheaf `E`, an epimorphism `e : E ⟶ G` and a morphism `h : E ⟶ A` with
`h ≫ p = e ≫ g`.

This is the key input of `lemma-flat-models-generators` [SGA 4½, Rapport, 4.6–4.8]: `G` is generated
by finitely many sections over affine étale `V ⟶ X`, their images in `B` lift to `A` after
refining each `V` by a finite affine étale cover, and `E` is the corresponding finite direct sum
of free sheaves `Λ[W] = j_{W!} Λ_W` on the affine étale `X`-schemes `W` of the refinements
(`AlgebraicGeometry.Etale.liftsAlongEpi_of_exists_epi_sigma_freeYoneda`). These are flat
(`AlgebraicGeometry.Etale.flat_freeYoneda`) and constructible
(`AlgebraicGeometry.Etale.isConstructibleSheaf_freeYoneda`), and the generation is
`AlgebraicGeometry.Etale.exists_jointlyEpi_freeYoneda`. -/
theorem liftsAlongEpi_flat_isConstructibleSheaf [Finite Λ] [IsNoetherian X] :
    ChainComplex.LiftsAlongEpi
      (fun F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        ObjectProperty.flat F ∧ IsConstructibleSheaf F)
      (fun F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦ IsConstructibleSheaf F) := by
  let S : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun F ↦ ObjectProperty.flat F ∧ IsConstructibleSheaf F
  have : S.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    have : IsConstructibleSheaf _ := h.2
    exact ⟨ObjectProperty.prop_of_iso _ e h.1, IsConstructibleSheaf.of_iso e⟩⟩
  have : S.ContainsZero := ⟨0, isZero_zero _, ObjectProperty.flat_of_isZero (isZero_zero _),
    IsConstructibleSheaf.of_isZero (isZero_zero _)⟩
  have := S.isClosedUnderFiniteCoproducts_of_biprod fun X Y hX hY ↦ by
    have : IsConstructibleSheaf X := hX.2
    have : IsConstructibleSheaf Y := hY.2
    exact ⟨ObjectProperty.flat_biprod hX.1 hY.1, IsConstructibleSheaf.biprod X Y⟩
  exact liftsAlongEpi_of_exists_epi_sigma_freeYoneda S _
    (fun W _ ↦ ⟨flat_freeYoneda W, isConstructibleSheaf_freeYoneda W⟩)
    (fun G hG ↦ by
      have : IsConstructibleSheaf G := hG
      exact exists_jointlyEpi_freeYoneda G)

open ZeroObject in
/-- Blueprint `lemma-flat-models-generators` (also `lemma-flat-models-generators--1`): Bounded flat
model of finite Tor amplitude

**Constructible variant.** Let `X` be Noetherian and `Λ` finite. For `K ∈ D^b_c(X, Λ)` and
integers `a ≤ b`, `K` has Tor amplitude in `[a, b]` if and only if it is isomorphic to a bounded
flat complex `P` in degrees `[a, b]` whose terms are *constructible*. In particular every object
of `Dctf(X, Λ)` has such a model.

The flat model of `hasTorAmplitudeIn_iff_exists_flatModel` is built from a bounded above
resolution of `K` by flat constructible sheaves
(`DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi`), which exists
because flat constructible sheaves lift along epimorphisms onto constructible sheaves
(`AlgebraicGeometry.Etale.liftsAlongEpi_flat_isConstructibleSheaf`) and constructible sheaves
are closed under kernels and cokernels (`Scheme.IsConstructibleSheaf.kernel`,
`Scheme.IsConstructibleSheaf.cokernel`): its truncation in degree `a` is then a cokernel of a
map of constructible sheaves, hence flat and constructible. The converse is the corresponding
direction of `hasTorAmplitudeIn_iff_exists_flatModel`. The statement is made for a finite ring
`Λ`, as in the blueprint. -/
theorem hasTorAmplitudeIn_iff_exists_flatConstructibleModel [Finite Λ] [IsNoetherian X]
    (a b : ℤ) (hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K ↔
      ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
        IsBoundedFlatComplex Λ a b P ∧ (∀ q : ℤ, IsConstructibleSheaf (P.X q)) ∧
        Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  let T : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun F ↦ IsConstructibleSheaf F
  let S : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun F ↦ ObjectProperty.flat F ∧ IsConstructibleSheaf F
  have : T.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    have : IsConstructibleSheaf _ := h
    exact IsConstructibleSheaf.of_iso e⟩
  have : S.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    have : IsConstructibleSheaf _ := h.2
    exact ⟨ObjectProperty.prop_of_iso _ e h.1, IsConstructibleSheaf.of_iso e⟩⟩
  have : T.ContainsZero := ⟨0, isZero_zero _, IsConstructibleSheaf.of_isZero (isZero_zero _)⟩
  have : S.ContainsZero := ⟨0, isZero_zero _, ObjectProperty.flat_of_isZero (isZero_zero _),
    IsConstructibleSheaf.of_isZero (isZero_zero _)⟩
  have : T.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, hX, hY⟩
    have : IsConstructibleSheaf _ := hX
    have : IsConstructibleSheaf _ := hY
    have := IsConstructibleSheaf.kernel f
    exact IsConstructibleSheaf.of_iso (F := kernel f)
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk)⟩
  have : T.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hX, hY⟩
    have : IsConstructibleSheaf _ := hX
    have : IsConstructibleSheaf _ := hY
    have := IsConstructibleSheaf.cokernel f
    exact IsConstructibleSheaf.of_iso (F := cokernel f)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hk)⟩
  constructor
  · intro h
    rw [DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn] at h
    obtain ⟨P, _, _, hP, ⟨e⟩⟩ :=
      _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi
        (S := S) (T := T) (fun _ h ↦ h.2) (fun _ h ↦ h.1)
        (fun X Y hX hY ↦ by
          have : IsConstructibleSheaf X := hX.2
          have : IsConstructibleSheaf Y := hY.2
          exact ⟨ObjectProperty.flat_biprod hX.1 hY.1, IsConstructibleSheaf.biprod X Y⟩)
        (liftsAlongEpi_flat_isConstructibleSheaf Λ) h (fun n ↦ hK.2 n)
    exact ⟨P, isBoundedFlatComplex_iff.2 ⟨inferInstance, inferInstance, fun q ↦ (hP q).1⟩,
      fun q ↦ (hP q).2, ⟨e.symm⟩⟩
  · rintro ⟨P, hP, -, he⟩
    exact (hasTorAmplitudeIn_iff_exists_flatModel Λ a b hab K hK).2 ⟨P, hP, he⟩

end Etale

end AlgebraicGeometry
