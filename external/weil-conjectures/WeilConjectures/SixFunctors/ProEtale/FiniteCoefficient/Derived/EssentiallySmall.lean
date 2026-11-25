/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.EssentiallySmall
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Presentation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-!
# `Dctf(X, Λ)` is essentially small

Blueprint `lemma-hypotheses-brown-representability--5`. On a quasi-compact quasi-separated scheme
`X`, a constructible étale sheaf of modules over a noetherian ring `Λ` is the cokernel of a map
between finite sums of extensions by zero `v_! Λ` along étale maps (Stacks 095N,
`AlgebraicGeometry.Etale.exists_presentation_of_isConstructibleSheaf`); such data form a set, so
the constructible sheaves are essentially small
(`AlgebraicGeometry.Etale.essentiallySmall_constructibleSheaf`). By induction along the truncation
triangles, so are the bounded constructible étale complexes
(`AlgebraicGeometry.Etale.DerivedCategory.essentiallySmall_boundedConstructible`), and hence the
bounded constructible pro-étale complexes, which are their images under `ν^*`, and `Dctf(X, Λ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.essentiallySmall_constructibleFiniteTor`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ] (X : Scheme.{u})
  [CompactSpace X] [QuasiSeparatedSpace X]

namespace Etale

/-- The finite sums `∐ᵢ (wᵢ)_! Λ` of extensions by zero of the constant sheaf along étale
maps `wᵢ : Uᵢ ⟶ X`. -/
noncomputable def sigmaEtaleLowerShriekConstant
    (k : Σ (n : ℕ) (U : Fin n → Scheme.{u}), {w : ∀ i, U i ⟶ X // ∀ i, Etale (w i)}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ∐ fun i ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (k.2.2.1 i) (k.2.2.2 i)).obj
    ((constantSheaf (k.2.1 i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))

/-- Blueprint `lemma-hypotheses-brown-representability--5`: the constructible étale sheaves of
modules over a noetherian ring on a quasi-compact quasi-separated scheme are essentially small. -/
instance essentiallySmall_constructibleSheaf :
    ObjectProperty.EssentiallySmall.{u + 1}
      (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X) := by
  let κ := Σ (n : ℕ) (U : Fin n → Scheme.{u}), {w : ∀ i, U i ⟶ X // ∀ i, Etale (w i)}
  let ι := Σ (k₁ k₀ : κ),
    (sigmaEtaleLowerShriekConstant Λ X k₁ ⟶ sigmaEtaleLowerShriekConstant Λ X k₀)
  let S (x : ι) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := cokernel x.2.2
  refine ⟨ObjectProperty.ofObj S, inferInstance, fun F hF ↦ ?_⟩
  have : IsConstructibleSheaf F := hF
  obtain ⟨m, n, V, v, hv, -, U, w, hw, -, φ, π, hφπ, ⟨hc⟩⟩ :=
    exists_presentation_of_isConstructibleSheaf F
  let x : ι := ⟨⟨m, V, v, hv⟩, ⟨n, U, w, hw⟩, φ⟩
  exact ⟨S x, ObjectProperty.ofObj_apply S x,
    ⟨hc.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

instance : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, IsConstructibleSheaf.of_isZero (isZero_zero _)⟩

/-- Blueprint `lemma-hypotheses-brown-representability--5`: the bounded constructible étale
complexes on a quasi-compact quasi-separated scheme are essentially small. -/
instance DerivedCategory.essentiallySmall_boundedConstructible :
    ObjectProperty.EssentiallySmall.{u + 1}
      (Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X) :=
  inferInstanceAs (ObjectProperty.EssentiallySmall.{u + 1}
    (_root_.DerivedCategory.TStructure.t.bounded ⊓ _root_.DerivedCategory.homologyProperty
      (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X)))

end Etale

namespace ProEtale

/-- Blueprint `lemma-hypotheses-brown-representability--5`: `Dctf(X, Λ)` is essentially small, for a
quasi-compact quasi-separated scheme `X`. -/
instance DerivedCategory.essentiallySmall_constructibleFiniteTor :
    ObjectProperty.EssentiallySmall.{u + 1}
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X) :=
  have : ObjectProperty.EssentiallySmall.{u + 1}
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X) :=
    inferInstanceAs (ObjectProperty.EssentiallySmall.{u + 1}
      ((Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).map _))
  ObjectProperty.EssentiallySmall.of_le inf_le_left

/-- A small skeleton of `Dctf(X, Λ)`: a family indexed by a type in `Type (u + 1)` of objects of
`Dctf(X, Λ)` containing a representative of every isomorphism class. -/
theorem DerivedCategory.exists_skeleton_constructibleFiniteTor :
    ∃ (ι : Type (u + 1)) (S : ι → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ))),
      (∀ i, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (S i)) ∧
      ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        ∃ i, Nonempty (S i ≅ K) := by
  obtain ⟨Q, _, hQ, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u + 1}
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X)
  refine ⟨Shrink.{u + 1} (Subtype Q), fun i ↦ ((equivShrink _).symm i).1,
    fun i ↦ hQ _ ((equivShrink _).symm i).2, fun K hK ↦ ?_⟩
  obtain ⟨Y, hY, ⟨e⟩⟩ := hP K hK
  exact ⟨equivShrink _ ⟨Y, hY⟩, ⟨by simpa using e.symm⟩⟩

end ProEtale

end AlgebraicGeometry
