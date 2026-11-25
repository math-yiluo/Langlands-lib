/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars

/-! # Canonical types for finite coefficient restriction comparisons

Source: the current blueprint finite-level coefficient comparison; Stacks Tag 03DA
(blueprint: def-coef-compact-support-coefficient-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

/-- Existing derived restriction with canonical constant-coefficient category types.
Source: Stacks Tag 03DA
(blueprint: def-coef-compact-support-coefficient-presentation). -/
def compactSupportCoefficientRestriction (W : Scheme.{u}) (φ : A →+* B) :
    proEtaleDerivedCategory W B ⥤ proEtaleDerivedCategory W A :=
  (proEtaleCoefficientRestrictScalars W φ).mapDerivedCategory

/-- The specified identity restriction comparison, including a given ring-map equality.
Source: Stacks Tag 03DA
(blueprint: def-coef-compact-support-coefficient-presentation). -/
def compactSupportCoefficientResId (W : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (q : A →+* A) (hq : q = RingHom.id A) :
    compactSupportCoefficientRestriction W q ≅ 𝟭 _ :=
  eqToIso (congrArg
    (fun q ↦ (proEtaleCoefficientRestrictScalars W q).mapDerivedCategory) hq) ≪≫
      sfOpenDerivedCoefficientRestrictionId W A

/-- The specified composition comparison with its prescribed direct-map equality cast.
Source: Stacks Tag 03DA
(blueprint: def-coef-compact-support-coefficient-presentation). -/
def compactSupportCoefficientResComp (W : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : ψ.comp φ = χ) :
    compactSupportCoefficientRestriction W ψ ⋙
        compactSupportCoefficientRestriction W φ ≅
      compactSupportCoefficientRestriction W χ :=
  sfDerivedCoefficientRestrictionComp W φ ψ ≪≫
    eqToIso (congrArg
      (fun q ↦ (proEtaleCoefficientRestrictScalars W q).mapDerivedCategory) hχ)

/-- The existing compact-support coefficient comparison in the same category types.
Source: Stacks Tags 03DI and 03DA
(blueprint: def-coef-compact-support-coefficient-presentation). -/
def compactSupportCoefficientComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (φ : A →+* B) :
    compactSupportCoefficientRestriction X φ ⋙ sfAmbientCompactSupportCandidate A c ≅
      sfAmbientCompactSupportCandidate B c ⋙ compactSupportCoefficientRestriction Y φ :=
  sfCompactSupportRestriction c φ

theorem compactSupportQuotient_intrinsic_eq_ambient
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (A : Type u) [CommRing A] [Finite A] :
    sfIntrinsicCompactSupport c A = sfAmbientCompactSupportCandidate A c := by
  unfold sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  rfl

end WeilConjectures
