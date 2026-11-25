/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedScheme
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Cohomological correspondences

Let `X` be a scheme over a base `s` with structure morphism `aX : X ⟶ s`, and `K` an object of
the derived category `D(X_ét, Λ)` of étale sheaves of modules over a finite ring `Λ`. A
*cohomological correspondence* on `K` is a scheme `C` with two morphisms `c₁ c₂ : C ⟶ X` over
`s`, i.e. `c = (c₁, c₂) : C ⟶ X ×_s X`, together with a morphism `u : c₂^* K ⟶ Rc₁^! K` in
`D(C_ét, Λ)`. Here `c₂` is the pullback leg and `c₁` the exceptional leg. The *graph
correspondence* of an endomorphism `h : X ⟶ X` over `s` and a morphism `v : h^* K ⟶ K` is
`C = X`, `c₁ = 𝟙`, `c₂ = h`, `u = v`; its fixed scheme is the fixed scheme `Fix(h)` of `h`.

## Main definitions

- `AlgebraicGeometry.Etale.CohomologicalCorrespondence`: a cohomological correspondence
  (blueprint `definition-correspondence--2`).
- `AlgebraicGeometry.Etale.CohomologicalCorrespondence.fixedScheme`: its fixed scheme
  `Fix(c) = C ×_{X ×_s X, c, Δ_X} X` (blueprint `definition-correspondence--3`).
- `AlgebraicGeometry.Etale.CohomologicalCorrespondence.graph`: the graph correspondence of
  `(h, v)` (blueprint `definition-frobenius-correspondences-their-operators--5`), whose fixed scheme
  is `Fix(h)` (`AlgebraicGeometry.Etale.CohomologicalCorrespondence.fixedScheme_graph`).

## Implementation notes

The pullback leg is the derived pullback `D((c₂)^*[ModuleCat Λ])` along `c₂`, which is the derived
functor `L((c₂)^*[ModuleCat Λ])` since `c₂^*` is exact
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`). The exceptional leg is the
exceptional inverse image `R(c₁)^![Λ]`, which needs `c₁` to admit a compactification; this is
recorded as an instance field. The blueprint's admissibility of `c₁`
(`theorem-f-shriek-finite-coefficients`, the existence of the adjunction `Rc₁_! ⊣ Rc₁^!` with its
exchange isomorphisms) is a theorem for separated finite type morphisms, and is not part of the
data.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X s : Scheme.{u}} (aX : X ⟶ s)
  (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- Blueprint `definition-correspondence--2`: Cohomological correspondence.

A cohomological correspondence on an object `K` of `D(X_ét, Λ)`, for `X` over `s` via `aX`: a
separated scheme `C` of finite type over `s` with morphisms `c = (c₁, c₂) : C ⟶ X ×_s X`, that
is `c₁ c₂ : C ⟶ X` with `c₁ ≫ aX = c₂ ≫ aX`, and a morphism `u : c₂^* K ⟶ Rc₁^! K` in
`D(C_ét, Λ)`. The leg `c₂` is the pullback leg and `c₁` the exceptional leg. -/
structure CohomologicalCorrespondence where
  /-- The correspondence scheme `C`. -/
  C : Scheme.{u}
  /-- The exceptional leg `c₁ : C ⟶ X`. -/
  c₁ : C ⟶ X
  /-- The pullback leg `c₂ : C ⟶ X`. -/
  c₂ : C ⟶ X
  /-- The two legs are morphisms over `s`, so that `c = (c₁, c₂) : C ⟶ X ×_s X`. -/
  w : c₁ ≫ aX = c₂ ≫ aX
  /-- `C` is separated over `s`. -/
  isSeparated : IsSeparated (c₁ ≫ aX)
  /-- `C` is locally of finite type over `s`. -/
  locallyOfFiniteType : LocallyOfFiniteType (c₁ ≫ aX)
  /-- `C` is quasi-compact over `s`. -/
  quasiCompact : QuasiCompact (c₁ ≫ aX)
  /-- The exceptional leg admits a compactification. -/
  [hasCompactification : HasCompactification c₁]
  /-- The cohomological correspondence `u : c₂^* K ⟶ Rc₁^! K`. -/
  u : (D((c₂)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (R(c₁)^![Λ]).obj K

namespace CohomologicalCorrespondence

attribute [instance] hasCompactification

variable {Λ aX K} (c : CohomologicalCorrespondence Λ aX K)

/-- The fixed scheme `Fix(c) = C ×_{X ×_s X, c, Δ_X} X` of a cohomological correspondence
(blueprint `definition-correspondence--3`). -/
noncomputable abbrev fixedScheme : Scheme.{u} :=
  Scheme.fixedScheme aX c.c₁ c.c₂ c.w

section Graph

variable (Λ)

/-- Blueprint `definition-frobenius-correspondences-their-operators--5`: Graph correspondence.

The graph correspondence of a separated finite type endomorphism `h : X ⟶ X` over `s` and a
morphism `v : h^* K ⟶ K`: `C = X`, `c₁ = 𝟙 X`, `c₂ = h` and `u = v`, composed with the
identification `R(𝟙 X)^! ≅ 𝟭` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`). Its
fixed scheme is `Fix(h)` (`fixedScheme_graph`). -/
noncomputable def graph [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (h : X ⟶ X) (hh : h ≫ aX = aX) (v : (D((h)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    CohomologicalCorrespondence Λ aX K where
  C := X
  c₁ := 𝟙 X
  c₂ := h
  w := by rw [hh, Category.id_comp]
  isSeparated := by rwa [Category.id_comp]
  locallyOfFiniteType := by rwa [Category.id_comp]
  quasiCompact := by rwa [Category.id_comp]
  u := v ≫ (rightDerivedUpperShriekIdIso Λ X).inv.app K

variable {Λ} [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]

@[simp]
lemma graph_C (h : X ⟶ X) (hh : h ≫ aX = aX) (v : (D((h)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (graph Λ h hh v).C = X :=
  rfl

@[simp]
lemma graph_c₁ (h : X ⟶ X) (hh : h ≫ aX = aX) (v : (D((h)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (graph Λ h hh v).c₁ = 𝟙 X :=
  rfl

@[simp]
lemma graph_c₂ (h : X ⟶ X) (hh : h ≫ aX = aX) (v : (D((h)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (graph Λ h hh v).c₂ = h :=
  rfl

/-- The fixed scheme of the graph correspondence of `h` is the fixed scheme `Fix(h)` of `h`,
the scheme-theoretic equalizer of `𝟙 X` and `h` (blueprint
`definition-frobenius-correspondences-their-operators--5`). -/
lemma fixedScheme_graph (h : X ⟶ X) (hh : h ≫ aX = aX)
    (v : (D((h)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (graph Λ h hh v).fixedScheme = Hom.fixedScheme aX h hh :=
  rfl

end Graph

end CohomologicalCorrespondence

end AlgebraicGeometry.Etale
