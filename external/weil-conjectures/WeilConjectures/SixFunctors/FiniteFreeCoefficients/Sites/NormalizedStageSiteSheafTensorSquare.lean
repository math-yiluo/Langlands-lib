/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-!
# Underived sheaf monoidal square for scalar/site comparison

Source: Stacks Project, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback;
scalar/site specialization and pure-tensor reassociation in the latest blueprint
lemma-change-coefficients-exceptional-inverse-image--3, paragraph 3.
(blueprint: lem-sf-normalized-stage-site-sheaf-tensor-square)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace WeilConjectures.FiniteFreeCoefficients.Sites

attribute [local instance] Sheaf.monoidalCategory
-- Use the site's direct monoidal sheafification instance, as in ScalarExtensionMonoidal.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

/-- The existing sheafified scalar balancing tensorator, specialized to the etale site.
Source: Stacks 03EK; `composeAndSheafifyOplaxMonoidal`.
(blueprint: lem-sf-normalized-stage-site-sheaf-tensor-square). -/
-- This is definitionally the project's ordinary scalar tensorator; the local instance
-- avoids importing derived exceptional-coefficient constructions for an underived square.
local instance etaleScalarOplax {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

-- The etale scalar tensorator is the project instance
-- `AlgebraicGeometry.Etale.ExceptionalCoefficients.ordinaryOplax` (the sheafified scalar
-- balancing map), the same construction as the pro-etale instance
-- `AlgebraicGeometry.ProEtale.oplaxMonoidal_sheafExtendScalars`.

/-- The ordinary scalar/site comparison square commutes on module sheaves.

Source: Stacks Project, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback;
scalar/site specialization and pure-tensor reassociation in the latest blueprint
lemma-change-coefficients-exceptional-inverse-image--3, paragraph 3.
(blueprint: lem-sf-normalized-stage-site-sheaf-tensor-square)

Proof:
1. Unpack the ordinary comparison data: `ν^*` on `A`- and `B`-module sheaves, the two
   sheafified scalar extensions with their normalized tensor maps `μ`, and the scalar/site
   mate `σ`, the inverse of `etaleSheafExtendScalarsCompComparisonUpperStarIso`. Both
   composites are maps `S^pro ν_A (M ⊗ N) ⟶ ν_B S^et M ⊗ ν_B S^et N`.
2. The oplax map `τ` of `ν^*` (Stacks 03EL) carries `ν(x ⊗ y)` to `ν x ⊗ ν y` on étale
   sections `x`, `y`, naturally in module maps and under restriction.
3. Compute the mate with unit and counit: `σ = (ε₂ ν_B S^et) ∘ (S^pro β S^et) ∘ (S^pro ν_A η₁)`
   for the restriction comparison `β`, so `σ (b ⊗ ν_A x) = b • ν_B (1 ⊗ x)`; the normalized
   scalar tensor map sends `s ⊗ (x ⊗ y)` to `(s ⊗ x) ⊗ (1 ⊗ y)` on both sites.
4. Transpose under the composite adjunction `S^pro ν_A ⊣ ν_{A,*} R₂`: a map out of
   `S^pro ν_A (M ⊗ N)` is determined by its values on `1 ⊗ ν_A z`, and by the sheafification
   universal property on étale pure tensors `z = x ⊗ y`. Both routes send
   `1 ⊗ ν_A (x ⊗ y)` to `ν_B (1 ⊗ x) ⊗ ν_B (1 ⊗ y)`; by `B`-linearity both send
   `b ⊗ (m ⊗ n)` to `(b ⊗ m) ⊗ (1 ⊗ n)`.
This uses no nonzero-ring, flatness, point, or nonempty-site hypothesis, and includes zero
sheaves and the identity ring map.
-/
theorem normalized_stage_site_sheaf_tensor_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.sheafExtendScalars φ X).map
          (Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X) M N) ≫
        Functor.OplaxMonoidal.δ (ProEtale.sheafExtendScalars φ X)
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M)
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj N) ≫
        ((ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).inv.app M ⊗ₘ
          (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).inv.app N) =
      (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).inv.app (M ⊗ N) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).map
          (Functor.OplaxMonoidal.δ (ProEtale.etaleSheafExtendScalars φ X) M N) ≫
        Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
          ((ProEtale.etaleSheafExtendScalars φ X).obj M)
          ((ProEtale.etaleSheafExtendScalars φ X).obj N) := by
  let := ProEtale.laxMonoidal_sheafComposeRestrictScalars φ X
  let : (sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1} φ)).LaxMonoidal :=
    sheafComposeLaxMonoidal _ _
  have hβ : NatTrans.IsMonoidal
      (ProEtale.comparisonLowerStarCompSheafComposeRestrictScalarsIso φ X).hom := by
    exact Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
      X.toProEt X.smallEtaleTopology (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)
  let := hβ
  let : (ProEtale.etaleSheafExtendScalarsAdjunction φ X).IsMonoidal :=
    isMonoidal_sheafAdjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  have h := conjugateEquiv_symm_app_tensor_comp_δ
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X))
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
      (ProEtale.sheafExtendScalarsAdjunction φ X))
    (ProEtale.comparisonLowerStarCompSheafComposeRestrictScalarsIso φ X).hom M N
  simpa only [ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso,
    conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv,
    Functor.OplaxMonoidal.comp_δ, Category.assoc] using h.symm

end WeilConjectures.FiniteFreeCoefficients.Sites
