/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Restricted pushforward under its preservation hypothesis

Source: the blueprint, `chap-Construction-of-f`, restriction paragraph of
`sk-def-sfb-dc-restricted-functors` (blueprint: sk-def-sfb-dc-restricted-functors).

The imported module supplies all the restricted operations and their structural maps for
its named coefficient classes. Here the same restriction and restricted adjunction are
constructed from preservation itself, allowing arbitrary commutative condensed coefficients.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Preservation by every derived pushforward between separated finite-type `k`-schemes.
This is precisely the conditional hypothesis in the blueprint restriction paragraph,
not a restriction to one of its example coefficient rings.
Source: blueprint `sk-def-sfb-dc-restricted-functors`
(blueprint: sk-def-sfb-dc-restricted-functors). -/
def PreservesBoundedConstructiblePushforwards (k : Type u) [Field k] : Prop :=
  ∀ {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (K : ProEtale.BoundedConstructible (condensedRingObj Λ X.left)),
    boundedConstructible (condensedRingObj Λ Y.left) ((R((f.left)_*⟦Λ⟧)).obj K.obj)

variable {k : Type u} [Field k]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (H : PreservesBoundedConstructiblePushforwards Λ k) (f : X ⟶ Y)

/-- Restrict the ambient derived pushforward, using the stated preservation hypothesis.
Its object and morphism data are those of the ambient functor, with only the object property
supplied by `H`. Source: blueprint restriction paragraph
(blueprint: sk-def-sfb-dc-restricted-functors). -/
noncomputable def boundedConstructibleLowerStarOfPreserves :
    ProEtale.BoundedConstructible (condensedRingObj Λ X.left) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ Y.left) :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧))
    (fun K ↦ H f K)

/-- The conditional restriction commutes with the fully faithful inclusions.
Source: blueprint restriction paragraph (blueprint: sk-def-sfb-dc-restricted-functors). -/
noncomputable def boundedConstructibleLowerStarOfPreservesCompatibility :
    boundedConstructibleLowerStarOfPreserves Λ H f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((f.left)_*⟦Λ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- Restrict the actual ambient derived pullback--pushforward adjunction along the fully
faithful inclusions; thus its unit and counit are the restricted ambient unit and counit.
Source: blueprint adjunction paragraph (blueprint: sk-def-sfb-dc-restricted-functors). -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves :
    boundedConstructibleUpperStar Λ ℓ f ⊣ boundedConstructibleLowerStarOfPreserves Λ H f :=
  Adjunction.restrictFullyFaithful (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (boundedConstructibleLowerStarOfPreservesCompatibility Λ H f).symm

end AlgebraicGeometry.ProEtale.CondensedRing
